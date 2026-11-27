#!/usr/bin/env python3
"""pp-step: submit one Standard ML phrase to a resident ProofPower session.

The first invocation on a checkout starts pp on that checkout's spade.polydb.
Later invocations use the same process. One phrase is one invocation.
"""

from __future__ import annotations

import argparse
import errno
import fcntl
import json
import os
import pty
import secrets
import select
import shutil
import signal
import socket
import subprocess
import sys
import threading
import time
from pathlib import Path

# ProofPower's defaults. Program output can contain them, so a session
# replaces both prompts before it accepts a caller's phrase.
DEFAULT_READY = b":) "
DEFAULT_CONT = b":# "
LOCK_NAME = "spade.pid"
SOCK_NAME = "spade.sock"
DB_NAME = "spade.polydb"
PHRASE_TIMEOUT = 120.0
START_TIMEOUT = 60.0


def fail(message: str, status: int = 1) -> None:
    print(message, file=sys.stderr)
    raise SystemExit(status)


def require_program(name: str) -> str:
    path = shutil.which(name)
    if path is None:
        fail(f"{name} is not on PATH")
    return path


def default_root() -> Path:
    run = subprocess.run(
        ["git", "rev-parse", "--show-toplevel"],
        capture_output=True,
        text=True,
    )
    if run.returncode != 0:
        fail("cannot find the checkout root; pass --root")
    return Path(run.stdout.strip())


def session_env(root: Path) -> dict[str, str]:
    env = os.environ.copy()
    if not env.get("PPCHARSET"):
        env["PPCHARSET"] = "utf8"
    kept: list[str] = []
    home_prefix = str(Path.home() / "git" / "SPaDE-")
    for part in env.get("PPDATABASEPATH", "").split(":"):
        if not part or part == str(root) or part.startswith(home_prefix):
            continue
        if part not in kept:
            kept.append(part)
    ppdir = env.get("PPDIR")
    if ppdir:
        dbdir = str(Path(ppdir) / "bld" / "db")
        if dbdir not in kept:
            kept.append(dbdir)
    env["PPDATABASEPATH"] = str(root) + ((":" + ":".join(kept)) if kept else "")
    return env


def ensure_database(root: Path, env: dict[str, str]) -> None:
    child = root / DB_NAME
    if child.is_file():
        return
    ppdir = env.get("PPDIR")
    if not ppdir:
        fail("PPDIR is not set")
    parent = Path(ppdir) / "bld" / "db" / "rbjhol.polydb"
    if not parent.is_file():
        fail(f"{parent} is not present")
    run = subprocess.run(
        ["pp_make_database", "-p", "rbjhol", "spade"],
        cwd=root,
        env=env,
        capture_output=True,
        text=True,
    )
    if run.returncode != 0 or not child.is_file():
        detail = (run.stderr or run.stdout or "pp_make_database failed").strip()
        fail(detail)


def read_frame(conn: socket.socket) -> dict:
    chunks = []
    need = 4
    while need:
        part = conn.recv(need)
        if not part:
            raise ConnectionError("short frame")
        chunks.append(part)
        need -= len(part)
    size = int.from_bytes(b"".join(chunks), "big")
    if size > 8_000_000:
        raise ConnectionError("frame too large")
    body = []
    need = size
    while need:
        part = conn.recv(min(need, 65536))
        if not part:
            raise ConnectionError("short frame")
        body.append(part)
        need -= len(part)
    return json.loads(b"".join(body).decode("utf-8"))


def write_frame(conn: socket.socket, payload: dict) -> None:
    body = json.dumps(payload).encode("utf-8")
    conn.sendall(len(body).to_bytes(4, "big") + body)


def echo_end(buf: bytes, sent: bytes, markers: tuple[bytes, ...]) -> int | None:
    """Index just after the echo of one sent line, skipping prompt markers."""
    index = 0
    limit = len(buf)
    for ch in sent:
        while index < limit:
            if ch == 0x0A and buf[index] == 0x0D:
                index += 1
                continue
            if buf[index] == ch:
                index += 1
                break
            skipped = False
            for marker in markers:
                if marker and buf.startswith(marker, index):
                    index += len(marker)
                    skipped = True
                    break
            if not skipped:
                return None
        else:
            return None
    return index


def prompt_is_complete(
    buf: bytes,
    ready: bytes,
    cont: bytes,
    sent: bytes | None,
    markers: tuple[bytes, ...],
) -> bool:
    if sent is None:
        return buf.endswith(ready) or buf.endswith(cont)
    end = echo_end(buf, sent, markers)
    if end is None:
        return False
    for prompt in (ready, cont):
        if buf.endswith(prompt) and len(buf) - len(prompt) >= end:
            return True
    return False


def read_until_prompt(
    master: int,
    timeout: float,
    buf: bytearray,
    ready: bytes,
    cont: bytes,
    sent: bytes | None = None,
    markers: tuple[bytes, ...] = (),
) -> None:
    deadline = time.monotonic() + timeout
    while True:
        if prompt_is_complete(buf, ready, cont, sent, markers):
            return
        if time.monotonic() > deadline:
            fail_text = buf.decode("utf-8", "replace")[-400:]
            raise TimeoutError(f"no prompt from pp within {timeout:.0f}s\n{fail_text}")
        readable, _, _ = select.select([master], [], [], 0.2)
        if not readable:
            continue
        try:
            chunk = os.read(master, 65536)
        except OSError as exc:
            raise RuntimeError(f"reading from pp failed: {exc}") from exc
        if not chunk:
            raise RuntimeError("pp closed its output")
        buf.extend(chunk)


def write_phrase(master: int, text: str, buf: bytearray, timeout: float) -> bytes:
    data = text.encode("utf-8")
    if not data.endswith(b"\n"):
        data += b"\n"
    view = memoryview(data)
    deadline = time.monotonic() + timeout
    while view:
        if time.monotonic() > deadline:
            raise TimeoutError("timed out sending a phrase to pp")
        _, writable, _ = select.select([], [master], [], 0.2)
        if master in select.select([master], [], [], 0)[0]:
            try:
                chunk = os.read(master, 65536)
            except OSError as exc:
                raise RuntimeError(f"reading from pp failed: {exc}") from exc
            if chunk:
                buf.extend(chunk)
        if not writable:
            continue
        wrote = os.write(master, view[:1024])
        view = view[wrote:]
    return data


class Session:
    def __init__(self, root: Path, env: dict[str, str]) -> None:
        self.root = root
        self.env = env
        self.master = -1
        self.proc: subprocess.Popen[bytes] | None = None
        self.buf = bytearray()
        self.token = secrets.token_hex(8)
        self.ready = f"@pp-step/{self.token}/ready ".encode()
        self.cont = f"@pp-step/{self.token}/more ".encode()

    def start(self) -> None:
        try:
            master, slave = pty.openpty()
        except OSError as exc:
            raise RuntimeError(f"pseudo-terminal: {exc}") from exc
        try:
            self.proc = subprocess.Popen(
                ["pp", "-d", "spade"],
                stdin=slave,
                stdout=slave,
                stderr=slave,
                cwd=self.root,
                env=self.env,
                start_new_session=True,
            )
        except OSError as exc:
            os.close(master)
            os.close(slave)
            raise RuntimeError(f"pp failed to start: {exc}") from exc
        os.close(slave)
        self.master = master
        read_until_prompt(master, START_TIMEOUT, self.buf, DEFAULT_READY, DEFAULT_CONT)
        self.buf.clear()
        # The marker is built by concatenation so its text is not in the
        # echoed source, where a short read could look like completion.
        setup = (
            "val _ = ("
            f'set_string_control ("prompt1", "@pp-" ^ "step/{self.token}" ^ "/rea" ^ "dy "); '
            f'set_string_control ("prompt2", "@pp-" ^ "step/{self.token}" ^ "/mo" ^ "re ")'
            ");"
        )
        self.submit(setup)
        self.buf.clear()

    def submit(self, text: str) -> str:
        assert self.master >= 0
        if not text.endswith("\n"):
            text += "\n"
        lines = text.split("\n")[:-1]
        markers = (self.ready, self.cont, DEFAULT_READY, DEFAULT_CONT)
        # A printed value sits between one line's echo and the next line's
        # echo. Match each line in its own buffer, then join them.
        parts: list[bytes] = []
        for line in lines:
            self.buf.clear()
            sent = write_phrase(self.master, line + "\n", self.buf, PHRASE_TIMEOUT)
            read_until_prompt(
                self.master,
                PHRASE_TIMEOUT,
                self.buf,
                self.ready,
                self.cont,
                sent,
                markers,
            )
            parts.append(bytes(self.buf))
        transcript = b"".join(parts)
        self.buf[:] = transcript
        return transcript.decode("utf-8")

    def stop(self) -> None:
        proc = self.proc
        self.proc = None
        if proc is not None:
            # `pp` is a shell script. Its SIGTERM trap exits the wrapper
            # and can leave the pp-ml child in this process group.
            if proc.poll() is None:
                try:
                    os.killpg(proc.pid, signal.SIGTERM)
                except OSError:
                    proc.terminate()
                try:
                    proc.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    pass
            try:
                os.killpg(proc.pid, signal.SIGKILL)
            except OSError:
                pass
            try:
                proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                pass
        if self.master >= 0:
            os.close(self.master)
            self.master = -1


def detach_stdio() -> None:
    """Drop the client's pipes so that process can exit while pp stays up."""
    devnull = os.open(os.devnull, os.O_RDWR)
    os.dup2(devnull, 0)
    os.dup2(devnull, 1)
    os.dup2(devnull, 2)
    if devnull > 2:
        os.close(devnull)


def serve(root: Path, lock_fd: int, env: dict[str, str]) -> None:
    sock_path = root / SOCK_NAME
    if sock_path.exists():
        sock_path.unlink()
    sock = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    sock.bind(str(sock_path))
    sock.listen(8)
    os.write(lock_fd, f"{os.getpid()}\n".encode())

    meta = threading.Lock()
    ready = threading.Event()
    stopped = threading.Event()
    released = threading.Event()
    replied = threading.Event()
    state = {"busy": False, "error": "", "waiter": False, "stopping": False, "closing": False}
    session: Session | None = None

    def refuse(conn: socket.socket, message: str) -> None:
        try:
            write_frame(conn, {"ok": False, "error": message})
        except OSError:
            pass

    def handle(conn: socket.socket) -> None:
        wait = False
        with conn:
            with meta:
                if state["closing"]:
                    refuse(conn, "database is in use")
                    return
                if state["error"]:
                    refuse(conn, state["error"])
                    stopped.set()
                    return
                if state["busy"] or (not ready.is_set() and state["waiter"]):
                    refuse(conn, "database is in use")
                    return
                state["busy"] = True
                if not ready.is_set():
                    state["waiter"] = True
                    wait = True
            try:
                if wait:
                    ready.wait()
                    with meta:
                        if state["closing"]:
                            refuse(conn, "database is in use")
                            return
                        if state["error"]:
                            refuse(conn, state["error"])
                            stopped.set()
                            return
                try:
                    request = read_frame(conn)
                except (ConnectionError, OSError, json.JSONDecodeError, UnicodeError):
                    return
                if request.get("cmd") == "stop":
                    state["stopping"] = True
                    stopped.set()
                    released.wait(timeout=15)
                    try:
                        write_frame(conn, {"ok": True, "text": ""})
                    except OSError:
                        pass
                    replied.set()
                    return
                if session is None:
                    refuse(conn, state["error"] or "pp did not start")
                    stopped.set()
                    return
                try:
                    text = session.submit(str(request.get("text", "")))
                except Exception as exc:
                    refuse(conn, str(exc))
                    stopped.set()
                    return
                try:
                    write_frame(conn, {"ok": True, "text": text})
                except (ConnectionError, OSError):
                    return
            except Exception as exc:
                refuse(conn, str(exc))
                stopped.set()
            finally:
                with meta:
                    state["busy"] = False

    def accept_loop() -> None:
        while not stopped.is_set():
            try:
                conn, _ = sock.accept()
            except OSError:
                break
            threading.Thread(target=handle, args=(conn,), daemon=True).start()

    threading.Thread(target=accept_loop, daemon=True).start()
    try:
        try:
            session = Session(root, env)
            session.start()
        except Exception as exc:
            state["error"] = str(exc)
            ready.set()
            stopped.wait(timeout=5)
            return
        ready.set()
        stopped.wait()
    finally:
        with meta:
            state["closing"] = True
        if session is not None:
            try:
                session.stop()
            except Exception:
                pass
        # Drop the listening name while the lock is still held. Releasing
        # the lock first lets a new session bind a socket this process then
        # unlinks, or lets that session connect to this one as it exits.
        try:
            sock.close()
        except OSError:
            pass
        try:
            sock_path.unlink()
        except OSError:
            pass
        try:
            os.close(lock_fd)
        except OSError:
            pass
        released.set()
        if state["stopping"]:
            replied.wait(timeout=5)


def call_session(root: Path, payload: dict, retry: bool) -> dict | None:
    sock_path = root / SOCK_NAME
    deadline = time.monotonic() + (START_TIMEOUT if retry else 1.0)
    while True:
        conn = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        try:
            try:
                conn.connect(str(sock_path))
            except (ConnectionError, FileNotFoundError, OSError) as exc:
                if not retry or time.monotonic() > deadline:
                    if retry:
                        fail(f"session failed to start: {exc}")
                    return None
                time.sleep(0.05)
                continue
            try:
                write_frame(conn, payload)
                return read_frame(conn)
            except Exception as exc:
                fail(f"pp-step failed after the phrase was sent: {exc}")
        finally:
            conn.close()


def acquire_lock(root: Path) -> int | None:
    fd = os.open(root / LOCK_NAME, os.O_CREAT | os.O_RDWR, 0o644)
    try:
        fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except OSError as exc:
        os.close(fd)
        if exc.errno in (errno.EAGAIN, errno.EWOULDBLOCK):
            return None
        raise
    os.ftruncate(fd, 0)
    return fd


def phrase_from(args: argparse.Namespace) -> str:
    if args.phrase is not None:
        return args.phrase
    if sys.stdin.isatty():
        fail("a phrase is required")
    return sys.stdin.read()


def main(argv: list[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description="Submit one phrase to a resident ProofPower session")
    parser.add_argument("phrase", nargs="?", help="one Standard ML phrase, or stop")
    parser.add_argument("--root", type=Path, help="checkout root (default: the git root)")
    args = parser.parse_args(argv)
    root = args.root.resolve() if args.root else default_root()
    if not root.is_dir():
        fail(f"{root} is not a directory")

    stopping = args.phrase == "stop"
    if stopping:
        reply = call_session(root, {"cmd": "stop"}, retry=False)
        if reply is None:
            fail("no session")
        if not reply.get("ok"):
            fail(str(reply.get("error") or "stop failed"))
        return

    require_program("pp")
    require_program("pp_make_database")
    text = phrase_from(args)
    sock_path = root / SOCK_NAME

    def deliver(reply: dict | None) -> bool:
        if reply is None:
            return False
        if not reply.get("ok"):
            fail(str(reply.get("error") or "pp-step failed"))
        sys.stdout.write(str(reply.get("text", "")))
        return True

    if sock_path.exists() and deliver(call_session(root, {"cmd": "eval", "text": text}, retry=False)):
        return

    lock_fd = acquire_lock(root)
    if lock_fd is None:
        if deliver(call_session(root, {"cmd": "eval", "text": text}, retry=False)):
            return
        fail("database is in use")

    env = session_env(root)
    ensure_database(root, env)
    pid = os.fork()
    if pid == 0:
        try:
            os.setsid()
            detach_stdio()
            serve(root, lock_fd, env)
        except Exception:
            os._exit(1)
        os._exit(0)
    os.close(lock_fd)
    reply = call_session(root, {"cmd": "eval", "text": text}, retry=True)
    if reply is None or not reply.get("ok"):
        fail(str((reply or {}).get("error") or "pp-step failed"))
    sys.stdout.write(str(reply.get("text", "")))
    sys.stdout.flush()


if __name__ == "__main__":
    main()
