"""
Low-level I/O module for SPaDE native repositories.
Handles binary files of null-terminated byte sequences.
"""
import os
from typing import Tuple, Optional, Union, List


class SPADEIORepository:
    """
    Low-level I/O module for SPaDE native repositories.
    Handles binary files of null-terminated byte sequences.
    Maintains file_pos (byte offset) and seq_count (sequence number).
    For reading: Loads into a dynamic list of bytes for structured access.
    """
    
    def __init__(self, filepath: str):
        self.filepath = filepath
        self._file = None  # File handle
        self.file_pos: int = 0
        self.seq_count: int = 0
        self._mode: Optional[str] = None  # 'r', 'w', 'a'
        self._sequences: List[bytes] = []  # For read mode: collected sequences

    def open_write(self) -> Tuple[int, int]:
        """Open new file for writing (overwrites if exists). Resets state."""
        if self._file:
            self.close()
        self._file = open(self.filepath, 'wb')
        self.file_pos = 0
        self.seq_count = 0
        self._mode = 'w'
        self._sequences.clear()
        return self.file_pos, self.seq_count

    def open_read(self) -> Tuple[int, int]:
        """Open existing file for reading. Starts at beginning; resets state."""
        if self._file:
            self.close()
        if not os.path.exists(self.filepath):
            raise FileNotFoundError(f"SPaDE repo not found: {self.filepath}")
        self._file = open(self.filepath, 'rb')
        self.file_pos = 0
        self.seq_count = 0
        self._mode = 'r'
        self._sequences.clear()
        return self.file_pos, self.seq_count

    def open_append(self) -> Tuple[int, int]:
        """Open for appending, but only if previously opened for read and at EOF."""
        if self._mode != 'r':
            raise ValueError("Append only allowed after read mode at EOF.")
        if self._file.tell() != os.path.getsize(self.filepath):
            raise ValueError("Append only allowed at end-of-file after read.")
        if self._file:
            self.close()
        self._file = open(self.filepath, 'ab')
        self.file_pos = self._file.tell()  # Should be EOF
        # seq_count unchanged—continues from read
        self._mode = 'a'
        return self.file_pos, self.seq_count

    def close(self) -> None:
        """Close the file handle. Safe to call multiple times."""
        if self._file:
            self._file.close()
            self._file = None
        self._mode = None

    def write_sequence(self, seq: Union[bytes, bytearray, str]) -> Tuple[int, int]:
        """Write a null-terminated byte sequence. seq can be bytes, bytearray, or str (auto-encoded as UTF-8).
        Returns updated (file_pos, seq_count).
        """
        if self._mode not in ('w', 'a'):
            raise ValueError("Write only in 'w' or 'a' mode.")
        if isinstance(seq, str):
            seq = seq.encode('utf-8')
        elif isinstance(seq, bytearray):
            seq = bytes(seq)
        # Ensure bytes
        if not isinstance(seq, bytes):
            raise TypeError("seq must be bytes, bytearray, or str.")
        null_terminated = seq + b'\x00'
        self._file.write(null_terminated)
        self.file_pos = self._file.tell()
        self.seq_count += 1
        return self.file_pos, self.seq_count

    def read_sequence(self) -> Tuple[bytes, int, int]:
        """Read next null-terminated byte sequence (excludes terminator).
        Returns (sequence_bytes, file_pos, seq_count).
        Raises EOFError if at end.
        """
        if self._mode != 'r':
            raise ValueError("Read only in 'r' mode.")
        seq = bytearray()
        while True:
            byte = self._file.read(1)
            if not byte:  # EOF
                if seq:  # Partial seq without null—error?
                    raise ValueError("Incomplete sequence at EOF (no null terminator).")
                raise EOFError("End of SPaDE repository reached.")
            if byte == b'\x00':
                break
            seq.append(byte[0])
        sequence = bytes(seq)  # To immutable bytes
        self._sequences.append(sequence)  # Collect for full read access
        self.file_pos = self._file.tell()
        self.seq_count += 1
        return sequence, self.file_pos, self.seq_count

    def read_all(self) -> List[bytes]:
        """Convenience: Read entire repository into list of bytes sequences.
        Efficient dynamic list appends; call after open_read().
        Returns list; updates seq_count to total.
        """
        if self._mode != 'r':
            raise ValueError("Read all only in 'r' mode.")
        self._sequences.clear()
        try:
            while True:
                self.read_sequence()
        except EOFError:
            pass
        return self._sequences

    def __enter__(self):
        """Context manager: Auto-open_read on enter."""
        self.open_read()
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        self.close()
