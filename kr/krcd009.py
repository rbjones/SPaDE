"""
    coded by Gemini 3 Pro (preview)
"""

import os
from typing import List, Tuple, Optional, Union, BinaryIO
from kr.krcd008 import EncodingDecodingABC, LowLevelIOABC, SExpressionsABC


class StaleCacheError(Exception):
    pass


class EncodingDecoding(EncodingDecodingABC):
    def _escape(self, data: bytes) -> bytes:
        """
        Helper to escape 0 as 1 0 and 1 as 1 1.
        Optimization: 1 is only escaped if it precedes 0 or 1.
        """
        out = bytearray()
        n = len(data)
        for i, b in enumerate(data):
            if b == 0:
                out.extend(b'\x01\x00')
            elif b == 1:
                # Check next byte
                if i + 1 < n:
                    next_b = data[i + 1]
                    if next_b == 0 or next_b == 1:
                        out.extend(b'\x01\x01')
                    else:
                        out.append(b)
                else:
                    # End of data. Will be followed by terminator (0).
                    # So 1 must be escaped to distinguish from 1 0 (escaped 0).
                    out.extend(b'\x01\x01')
            else:
                out.append(b)
        return bytes(out)

    def _unescape(self, data: bytes) -> bytes:
        """Helper to unescape 1 0 to 0 and 1 1 to 1."""
        out = bytearray()
        i = 0
        n = len(data)
        while i < n:
            b = data[i]
            if b == 1:
                i += 1
                if i >= n:
                    # Should not happen in valid stream
                    raise ValueError("Unexpected end of data after escape")
                next_b = data[i]
                if next_b == 0:
                    out.append(0)
                elif next_b == 1:
                    out.append(1)
                else:
                    # "When preceding a byte other than 0 or 1,
                    # binary 1 does not function as an escape"
                    out.append(1)
                    out.append(next_b)
            else:
                out.append(b)
            i += 1
        return bytes(out)

    def encode_bytes(self, data: bytes) -> bytes:
        """
        Encodes a byte sequence into a null-terminated byte sequence with escaping.
        Returns escaped_data + b'\0'.
        """
        return self._escape(data) + b'\x00'

    def decode_bytes(self, data: bytes) -> bytes:
        """
        Decodes a null-terminated byte sequence (excluding the null terminator)
        back into the original byte sequence.
        """
        return self._unescape(data)

    def encode_integer(self, value: int) -> bytes:
        """
        Encodes a positive integer to bytes (Big Endian).
        Note: The 'null-terminated' aspect is handled by the caller
        (LowLevelIO or encode_sequence_list).
        """
        # Calculate minimum bytes needed
        if value == 0:
            return b'\x00'
        length = (value.bit_length() + 7) // 8
        return value.to_bytes(length, byteorder='big')

    def decode_integer(self, data: bytes) -> int:
        """
        Decodes bytes to integer (Big Endian).
        """
        return int.from_bytes(data, byteorder='big')

    def encode_sequence_list(self, sequences: List[bytes]) -> bytes:
        """
        Encodes a list of byte sequences into a single byte sequence.
        Each sequence is converted to NTBS (escaped + \0) and concatenated.
        """
        out = bytearray()
        for seq in sequences:
            out.extend(self.encode_bytes(seq))
        return bytes(out)

    def decode_sequence_list(self, data: bytes) -> List[bytes]:
        """
        Decodes a payload (which is a concatenation of NTBSs) into a list of byte sequences.
        Cannot use simple split because 0 might appear in escape sequences (1 0).
        """
        sequences = []
        current_seq = bytearray()
        i = 0
        n = len(data)

        while i < n:
            b = data[i]
            if b == 1:
                # Escape sequence start
                current_seq.append(b)
                i += 1
                if i >= n:
                    raise ValueError("Unexpected end of data after escape in sequence list")
                current_seq.append(data[i])
            elif b == 0:
                # Terminator
                sequences.append(self.decode_bytes(current_seq))
                current_seq = bytearray()
            else:
                current_seq.append(b)
            i += 1

        # If data ended with 0, current_seq is empty and we successfully added the last item.
        # If data did NOT end with 0 (which shouldn't happen for valid NTBS concatenation),
        # we might have leftover bytes.
        # But encode_sequence_list always adds \0 at the end of each item.
        # So valid data should end with \0.
        # If current_seq is not empty here, it means the last item was not terminated.
        if len(current_seq) > 0:
            # This implies malformed data or missing terminator
            # But for robustness, maybe we assume implicit termination?
            # No, strict NTBS requires terminator.
            # However, split() logic would have ignored trailing empty string.
            # Let's raise error or ignore?
            # Given the strict format, let's assume valid data ends in 0.
            pass

        return sequences


class LowLevelIO(LowLevelIOABC):
    def __init__(self, encoding: Optional[EncodingDecodingABC] = None):
        self.encoding = encoding or EncodingDecoding()
        self.filepath: Optional[str] = None
        self._file: Optional[BinaryIO] = None
        self._cache: List[bytes] = []
        self._cache_map: dict = {}  # Map bytes -> seq_num
        self._mode: Optional[str] = None

    def open_new_repository(self, filepath: str, version: int = 1) -> None:
        self.filepath = filepath
        self._file = open(filepath, 'wb')
        self._mode = 'w'
        self._cache = []
        self._cache_map = {}

        # Write version
        ver_bytes = self.encoding.encode_integer(version)
        self.write_byte_sequence(ver_bytes)

    def open_existing_repository_read(self, filepath: str) -> None:
        self.filepath = filepath
        if self._file:
            self.close_repository()

        self._file = open(filepath, 'rb')
        self._mode = 'r'
        self._cache = []
        self._cache_map = {}

        # Read all
        try:
            while True:
                self.read_byte_sequence()
        except EOFError:
            pass

        # Reset to start? Or leave at end?
        # Usually we read to cache.
        # If we want to read again, we can seek 0.
        # But the method says "Reads and caches the entire repository".
        # So we are done.

    def open_existing_repository_append(self, filepath: str) -> None:
        if self._mode != 'r':
            raise ValueError("Must open for read before append")

        assert self._file is not None
        # Check file size
        current_pos = self._file.tell()
        file_size = os.path.getsize(filepath)

        if current_pos != file_size:
            raise StaleCacheError(f"File changed on disk. Read {current_pos}, Disk {file_size}")

        self._file.close()
        self._file = open(filepath, 'ab')
        self._mode = 'a'

    def close_repository(self) -> None:
        if self._file is not None:
            self._file.close()
            self._file = None
        self._mode = None

    def read_byte_sequence(self) -> Tuple[bytes, int]:
        if self._mode != 'r':
            raise ValueError("Not open for reading")

        assert self._file is not None
        # Read until unescaped 0
        buffer = bytearray()
        while True:
            b = self._file.read(1)
            if not b:
                raise EOFError()

            byte_val = b[0]

            if byte_val == 1:
                # Escape
                next_b = self._file.read(1)
                if not next_b:
                    raise ValueError("Unexpected EOF after escape")

                nb_val = next_b[0]
                if nb_val == 0:
                    buffer.append(0)
                elif nb_val == 1:
                    buffer.append(1)
                else:
                    buffer.append(1)
                    buffer.append(nb_val)
            elif byte_val == 0:
                # Terminator
                break
            else:
                buffer.append(byte_val)

        seq = bytes(buffer)
        seq_num = len(self._cache)
        self._cache.append(seq)
        self._cache_map[seq] = seq_num
        return seq, seq_num

    def write_byte_sequence(self, data: bytes) -> int:
        if self._mode not in ('w', 'a'):
            raise ValueError("Not open for writing/appending")

        if data in self._cache_map:
            return self._cache_map[data]

        assert self._file is not None
        # Encode
        encoded = self.encoding.encode_bytes(data)
        self._file.write(encoded)

        seq_num = len(self._cache)
        self._cache.append(data)
        self._cache_map[data] = seq_num
        return seq_num

    def get_sequence_number(self, data: bytes) -> Optional[int]:
        return self._cache_map.get(data)

    def get_byte_sequence(self, seq_num: int) -> bytes:
        return self._cache[seq_num]


class SExpressions(SExpressionsABC):
    def __init__(self, io: LowLevelIOABC, encoding: Optional[EncodingDecodingABC] = None):
        self.io = io
        self.encoding = encoding or EncodingDecoding()
        self.stack: List[int] = []

    def write_nil(self) -> int:
        # Nil is [b'\x02']
        payload = self.encoding.encode_sequence_list([b'\x02'])
        return self.io.write_byte_sequence(payload)

    def write_atom(self, value: bytes) -> int:
        # Atom is [b'\x03', value]
        payload = self.encoding.encode_sequence_list([b'\x03', value])
        return self.io.write_byte_sequence(payload)

    def write_cons(self, car_seq_num: int, cdr_seq_num: int) -> int:
        # Cons is [b'\x04', car_bytes, cdr_bytes]
        car_bytes = self.encoding.encode_integer(car_seq_num)
        cdr_bytes = self.encoding.encode_integer(cdr_seq_num)
        payload = self.encoding.encode_sequence_list([b'\x04', car_bytes, cdr_bytes])
        return self.io.write_byte_sequence(payload)

    def read_sexpression(self, seq_num: int) -> Union[None, bytes, Tuple[int, int]]:
        raw_payload = self.io.get_byte_sequence(seq_num)
        parts = self.encoding.decode_sequence_list(raw_payload)

        if not parts:
            raise ValueError("Empty S-expression payload")

        type_byte = parts[0]

        if type_byte == b'\x02':
            return None  # Nil
        elif type_byte == b'\x03':
            if len(parts) < 2:
                raise ValueError("Atom missing value")
            return parts[1]
        elif type_byte == b'\x04':
            if len(parts) < 3:
                raise ValueError("Cons missing pointers")
            car = self.encoding.decode_integer(parts[1])
            cdr = self.encoding.decode_integer(parts[2])
            return (car, cdr)
        else:
            raise ValueError(f"Unknown S-expression type: {type_byte!r}")

    def push_nil(self) -> None:
        seq = self.write_nil()
        self.stack.append(seq)

    def push_atom(self, value: bytes) -> None:
        seq = self.write_atom(value)
        self.stack.append(seq)

    def stack_cons(self) -> None:
        if len(self.stack) < 2:
            raise IndexError("Stack underflow for cons")
        # Top is CDR? Usually Cons(Car, Cdr). Stack: [..., Car, Cdr] -> Top is Cdr.
        cdr = self.stack.pop()
        car = self.stack.pop()
        seq = self.write_cons(car, cdr)
        self.stack.append(seq)

    def write_recursive(self, obj: Union[bytes, list, tuple, None]) -> int:
        """
        Recursively writes a Python object as S-expressions.
        bytes -> Atom
        None -> Nil
        tuple (car, cdr) -> Cons(car, cdr)
        list [a, b, ...] -> List (Cons chain ending in Nil)
        """
        if obj is None:
            return self.write_nil()
        elif isinstance(obj, bytes):
            return self.write_atom(obj)
        elif isinstance(obj, tuple):
            if len(obj) != 2:
                raise ValueError("Tuple must be length 2 for Cons")
            car_seq = self.write_recursive(obj[0])
            cdr_seq = self.write_recursive(obj[1])
            return self.write_cons(car_seq, cdr_seq)
        elif isinstance(obj, list):
            # Convert list to Cons chain
            # [A, B] -> Cons(A, Cons(B, Nil))
            # Iterate backwards
            current_seq = self.write_nil()
            for item in reversed(obj):
                item_seq = self.write_recursive(item)
                current_seq = self.write_cons(item_seq, current_seq)
            return current_seq
        else:
            raise TypeError(f"Unsupported type: {type(obj)}")

    def read_recursive(self, seq_num: int) -> Union[None, bytes, Tuple]:
        """
        Recursively reads S-expressions into Python objects.
        Nil -> None
        Atom -> bytes
        Cons -> (car, cdr)
        Note: Does not automatically convert Cons chains back to lists, returns nested tuples.
        """
        val = self.read_sexpression(seq_num)
        if val is None:
            return None
        elif isinstance(val, bytes):
            return val
        elif isinstance(val, tuple):
            car_seq, cdr_seq = val
            return (self.read_recursive(car_seq), self.read_recursive(cdr_seq))
        else:
            raise ValueError("Unknown value type")
