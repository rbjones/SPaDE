#!/usr/bin/env python3
"""Acceptance test for the resident ProofPower session (pp-step).

Run from a checkout, with PPDIR set and pp on PATH:

    python3 docs/admin/amte001.py
"""

from __future__ import annotations

import hashlib
import os
import shutil
import signal
import subprocess
import sys
import tempfile
import time
from pathlib import Path

SCRIPT = Path(__file__).resolve().parent / "amcd005.py"
FORBIDDEN = ("save_and_quit", "save_and_exit", "save")
SENT: list[str] = []


def fail(message: str) -> None:
    print(message, file=sys.stderr)
    raise SystemExit(1)


def require_environment() -> Path:
    ppdir = os.environ.get("PPDIR")
    if not ppdir:
        fail("PPDIR is not set")
    parent = Path(ppdir) / "bld" / "db" / "rbjhol.polydb"
    if not parent.is_file():
        fail(f"{parent} is not present")
    for name in ("pp", "pp_make_database"):
        if shutil.which(name) is None:
            fail(f"{name} is not on PATH")
    return parent


def digest(path: Path) -> bytes | None:
    if not path.exists():
        return None
    return hashlib.sha256(path.read_bytes()).digest()


def pp_pids(root: Path) -> list[int]:
    """Prover processes for this root.

    The `pp` on PATH is a shell wrapper. It stays in the foreground and
    runs `pp-ml` on the checkout database, with that directory as cwd.
    """
    found = []
    proc = Path("/proc")
    if not proc.is_dir():
        return found
    wanted = root.resolve()
    for entry in proc.iterdir():
        if not entry.name.isdigit():
            continue
        try:
            command = (entry / "cmdline").read_bytes().split(b"\0")
            cwd = Path(os.readlink(entry / "cwd")).resolve()
        except OSError:
            continue
        if not command or not command[0]:
            continue
        if Path(command[0].decode("utf-8", "replace")).name != "pp-ml":
            continue
        if cwd == wanted:
            found.append(int(entry.name))
    return found


def run(root: Path, phrase: str | None = None, stop: bool = False, check: bool = True) -> subprocess.CompletedProcess[str]:
    command = [sys.executable, str(SCRIPT), "--root", str(root)]
    if stop:
        command.append("stop")
    elif phrase is not None:
        SENT.append(phrase)
        command.append(phrase)
    try:
        result = subprocess.run(command, capture_output=True, text=True, timeout=180)
    except subprocess.TimeoutExpired:
        fail(f"{command} timed out")
    if check and result.returncode != 0:
        fail(f"{command} failed ({result.returncode})\n{result.stderr}\n{result.stdout}")
    return result


def lock_is_free(root: Path) -> bool:
    import fcntl

    fd = os.open(root / "spade.pid", os.O_CREAT | os.O_RDWR, 0o644)
    try:
        fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
        fcntl.flock(fd, fcntl.LOCK_UN)
        return True
    except BlockingIOError:
        return False
    finally:
        os.close(fd)


def stop_root(root: Path) -> None:
    subprocess.run([sys.executable, str(SCRIPT), "--root", str(root), "stop"], capture_output=True, text=True)
    for pid in pp_pids(root):
        try:
            os.kill(pid, signal.SIGTERM)
        except OSError:
            pass


def main() -> None:
    parent = require_environment()
    installed = Path(os.environ["PPDIR"]) / "bld" / "db" / "spade.polydb"
    before_parent = digest(parent)
    before_spade = digest(installed)
    if before_parent is None:
        fail(f"{parent} is not present")

    root = Path(tempfile.mkdtemp(prefix="amte001-"))
    other = Path(tempfile.mkdtemp(prefix="amte001-other-"))
    holder: subprocess.Popen[str] | None = None
    try:
        first = run(root, "val n = 1;")
        if "val n = 1" not in first.stdout:
            fail(f"binding was not reported\n{first.stdout}")
        second = run(root, "n + 1;")
        if "2" not in second.stdout:
            fail(f"n + 1 did not yield 2\n{second.stdout}")

        started = time.monotonic()
        partial = run(root, "val k =")
        elapsed = time.monotonic() - started
        if elapsed > 10:
            fail(f"continuation prompt took {elapsed:.1f}s")
        if ":#" not in partial.stdout:
            fail(f"continuation prompt was not returned\n{partial.stdout}")
        if not pp_pids(root):
            fail("pp exited at the continuation prompt")
        run(root, "1;")
        value = run(root, "k;")
        if "1" not in value.stdout:
            fail(f"k did not complete to 1\n{value.stdout}")

        run(root, 'open_theory "hol";')
        run(root, "set_goal([], \u231cT \u2227 T\u231d);")
        tactic = run(root, "a (strip_tac);")
        if "=== ProofPower" in tactic.stdout or "Database name:" in tactic.stdout:
            fail(f"tactic transcript contains a startup banner\n{tactic.stdout}")
        if "Tactic produced" not in tactic.stdout or "\u231cT\u231d" not in tactic.stdout:
            fail(f"tactic transcript is not the goal state\n{tactic.stdout}")

        accepted = run(root, "(* \u2502 *);")
        if "\u2502" not in accepted.stdout:
            fail(f"phrase containing │ was not accepted\n{accepted.stdout}")

        hold = "val _ = OS.Process.sleep (Time.fromReal 2.0);"
        SENT.append(hold)
        holder = subprocess.Popen(
            [sys.executable, str(SCRIPT), "--root", str(root), hold],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        )
        time.sleep(0.4)
        if holder.poll() is not None:
            out, err = holder.communicate()
            fail(f"the held phrase finished before a second call could overlap\n{err}\n{out}")
        SENT.append("0;")
        overlapped = subprocess.run(
            [sys.executable, str(SCRIPT), "--root", str(root), "0;"],
            capture_output=True,
            text=True,
            timeout=30,
        )
        if overlapped.returncode == 0:
            fail(f"an overlapping pp-step was accepted\n{overlapped.stdout}")
        if "database is in use" not in overlapped.stderr:
            fail(f"the refused call did not report that the database is in use\n{overlapped.stderr}")
        if len(pp_pids(root)) != 1:
            fail(f"a second pp was started: {pp_pids(root)}")
        out, err = holder.communicate(timeout=60)
        if holder.returncode != 0:
            fail(f"the held phrase failed ({holder.returncode})\n{err}\n{out}")
        holder = None

        other_result = run(other, "1 + 1;")
        if "2" not in other_result.stdout:
            fail(f"a session on another root was refused\n{other_result.stderr}")
        if len(pp_pids(other)) != 1 or len(pp_pids(root)) != 1:
            fail("the two roots do not have one pp each")
        run(other, stop=True)
        if pp_pids(other):
            fail("the other session's pp is still running")

        run(root, stop=True)
        if pp_pids(root):
            fail("pp is still running after stop")
        if not lock_is_free(root):
            fail("the lock was not released")
        if not (root / "spade.polydb").is_file():
            fail(f"database file is not {root / 'spade.polydb'}")

        again = run(root, "1 + 1;")
        if "2" not in again.stdout:
            fail(f"a new session did not start\n{again.stdout}")
        run(root, stop=True)

        for phrase in SENT:
            for word in FORBIDDEN:
                if word in phrase:
                    fail(f"the test sent {word}")
        if digest(parent) != before_parent:
            fail(f"{parent} changed")
        if digest(installed) != before_spade:
            if before_spade is None:
                fail(f"{installed} was created")
            fail(f"{installed} changed")
    finally:
        if holder is not None and holder.poll() is None:
            holder.kill()
            try:
                holder.wait(timeout=5)
            except subprocess.TimeoutExpired:
                pass
        stop_root(root)
        stop_root(other)
        shutil.rmtree(root, ignore_errors=True)
        shutil.rmtree(other, ignore_errors=True)
    print("amte001 passed")


if __name__ == "__main__":
    main()
