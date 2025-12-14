"""
SML-backed implementations of the Native Repository ABCs (krcd008.py).
A persistent ProofPower process is started, loads krcd011.sml, and communicates
via the NativeRepoService.repl loop using a simple ASCII protocol with hex-encoded
byte payloads.
"""
from __future__ import annotations

import subprocess
import threading
from pathlib import Path
from typing import List, Optional, Tuple, Union

from kr.krcd008 import EncodingDecodingABC, LowLevelIOABC, SExpressionsABC


class _PpSession:
    """Persistent ProofPower/PolyML session using the NativeRepoService in krcd011.sml."""

    def __init__(
        self,
        pp_cmd: Optional[str] = None,
        sml_path: Optional[Path] = None,
        database: str = "spade",
    ):
        self.pp_cmd = pp_cmd or "pp"
        self.database = database
        self.sml_path = sml_path or Path(__file__).resolve().parent / "krcd011.sml"
        self._proc: Optional[subprocess.Popen[str]] = None
        self._lock = threading.Lock()
        self._ensure_started()

    def _ensure_started(self) -> None:
        if self._proc and self._proc.poll() is None:
            return
        cmd = [self.pp_cmd, "-d", self.database]
        # Start pp; we will feed it the bootstrap to load krcd011.sml and enter the service loop
        self._proc = subprocess.Popen(
            cmd,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            bufsize=1,
        )
        assert self._proc.stdin and self._proc.stdout
        # Bootstrap: load the SML implementation and start the service loop
        bootstrap = (
            f'use "{self.sml_path}";\n'
            'print "READY\\n"; TextIO.flushOut TextIO.stdOut;\n'
            'NativeRepoService.repl();\n'
        )
        self._proc.stdin.write(bootstrap)
        self._proc.stdin.flush()
        # Drain until the READY marker to skip "val it = ()" noise from use
        while True:
            line = self._proc.stdout.readline()
            if line == "":
                raise RuntimeError("ProofPower session terminated during bootstrap")
            if line.strip() == "READY":
                break

    def _request(self, parts: List[str]) -> str:
        with self._lock:
            assert self._proc and self._proc.stdin and self._proc.stdout
            line = " ".join(parts) + "\n"
            self._proc.stdin.write(line)
            self._proc.stdin.flush()
            resp = self._proc.stdout.readline()
            if resp is None or resp == "":
                raise RuntimeError("ProofPower session terminated")
            if resp.startswith("OK "):
                return resp[3:].rstrip("\n")
            if resp.startswith("ERR "):
                raise RuntimeError(resp[4:].strip())
            raise RuntimeError(f"Unexpected response: {resp!r}")

    def stop(self) -> None:
        if self._proc and self._proc.poll() is None:
            try:
                self._proc.terminate()
            except Exception:
                pass


_session = _PpSession()


def _hex_encode(data: bytes) -> str:
    return data.hex()


def _hex_decode(text: str) -> bytes:
    return bytes.fromhex(text)


class EncodingDecodingSML(EncodingDecodingABC):
    def encode_bytes(self, data: bytes) -> bytes:
        return _hex_decode(_session._request(["ENCODE_BYTES", _hex_encode(data)]))

    def decode_bytes(self, data: bytes) -> bytes:
        return _hex_decode(_session._request(["DECODE_BYTES", _hex_encode(data)]))

    def encode_integer(self, value: int) -> bytes:
        return _hex_decode(_session._request(["ENCODE_INT", str(value)]))

    def decode_integer(self, data: bytes) -> int:
        return int(_session._request(["DECODE_INT", _hex_encode(data)]))

    def encode_sequence_list(self, sequences: List[bytes]) -> bytes:
        # Flatten by concatenating encoded items using the SML encoder to ensure consistency
        payload = b"".join(self.encode_bytes(seq) for seq in sequences)
        return payload

    def decode_sequence_list(self, data: bytes) -> List[bytes]:
        # Delegate to SML for correctness
        hex_payload = _hex_encode(data)
        parts_hex = _session._request(["DECODE_SEQ_LIST", hex_payload])
        if not parts_hex:
            return []
        return [_hex_decode(p) for p in parts_hex.split(",")]


class LowLevelIOSML(LowLevelIOABC):
    def __init__(self, encoding: Optional[EncodingDecodingABC] = None):
        self.encoding = encoding or EncodingDecodingSML()

    def open_new_repository(self, filepath: str, version: int = 1) -> None:
        _session._request(["OPEN_NEW", filepath, str(version)])

    def open_existing_repository_read(self, filepath: str) -> None:
        _session._request(["OPEN_READ", filepath])

    def open_existing_repository_append(self, filepath: str) -> None:
        _session._request(["OPEN_APPEND", filepath])

    def close_repository(self) -> None:
        _session._request(["CLOSE"])

    def read_byte_sequence(self) -> Tuple[bytes, int]:
        resp = _session._request(["READ_BSEQ"])
        num_str, hex_data = resp.split(" ", 1)
        return _hex_decode(hex_data), int(num_str)

    def write_byte_sequence(self, data: bytes) -> int:
        return int(_session._request(["WRITE_BSEQ", _hex_encode(data)]))

    def get_sequence_number(self, data: bytes) -> Optional[int]:
        resp = _session._request(["GET_SEQ", _hex_encode(data)])
        return None if resp == "NONE" else int(resp)

    def get_byte_sequence(self, seq_num: int) -> bytes:
        return _hex_decode(_session._request(["GET_BSEQ", str(seq_num)]))


class SExpressionsSML(SExpressionsABC):
    def __init__(
        self,
        io: Optional[LowLevelIOABC] = None,
        encoding: Optional[EncodingDecodingABC] = None,
    ):
        self.io = io or LowLevelIOSML(encoding=encoding)
        self.encoding = encoding or EncodingDecodingSML()

    def write_nil(self) -> int:
        return int(_session._request(["WRITE_NIL"]))

    def write_atom(self, value: bytes) -> int:
        return int(_session._request(["WRITE_ATOM", _hex_encode(value)]))

    def write_cons(self, car_seq_num: int, cdr_seq_num: int) -> int:
        return int(
            _session._request(["WRITE_CONS", str(car_seq_num), str(cdr_seq_num)])
        )

    def read_sexpression(self, seq_num: int) -> Union[None, bytes, Tuple[int, int]]:
        resp = _session._request(["READ_SEXP", str(seq_num)])
        if resp == "NIL":
            return None
        if resp.startswith("ATOM "):
            return _hex_decode(resp[5:])
        if resp.startswith("CONS "):
            _, a, b = resp.split(" ")
            return (int(a), int(b))
        raise RuntimeError(f"Unexpected S-expression response: {resp}")

    def push_nil(self) -> None:
        _session._request(["PUSH_NIL"])

    def push_atom(self, value: bytes) -> None:
        _session._request(["PUSH_ATOM", _hex_encode(value)])

    def stack_cons(self) -> None:
        _session._request(["STACK_CONS"])

    def write_recursive(self, obj: Union[bytes, list, tuple, None]) -> int:
        # Leverage the Python stacking helpers
        if obj is None:
            return self.write_nil()
        if isinstance(obj, bytes):
            return self.write_atom(obj)
        if isinstance(obj, tuple):
            if len(obj) != 2:
                raise ValueError("Tuple must be length 2 for Cons")
            car = self.write_recursive(obj[0])
            cdr = self.write_recursive(obj[1])
            return self.write_cons(car, cdr)
        if isinstance(obj, list):
            cur = self.write_nil()
            for item in reversed(obj):
                cur = self.write_cons(self.write_recursive(item), cur)
            return cur
        raise TypeError(f"Unsupported type: {type(obj)}")

    def read_recursive(self, seq_num: int) -> Union[None, bytes, Tuple]:
        val = self.read_sexpression(seq_num)
        if val is None:
            return None
        if isinstance(val, bytes):
            return val
        car, cdr = val
        return (self.read_recursive(car), self.read_recursive(cdr))


__all__ = [
    "EncodingDecodingSML",
    "LowLevelIOSML",
    "SExpressionsSML",
]
