"""
    coded by Gemini 3 Pro (preview)
"""

from abc import ABC, abstractmethod
from typing import List, Tuple, Optional, Union


class EncodingDecodingABC(ABC):
    """
    Abstract Base Class for Encoding/Decoding module.
    Handles escaping of null bytes and encoding of primitives.
    """
    @abstractmethod
    def encode_bytes(self, data: bytes) -> bytes:
        """
        Encodes a byte sequence into a null-terminated byte sequence with escaping.
        Binary 1 is used as escape character (only if needed).
        """
        pass

    @abstractmethod
    def decode_bytes(self, data: bytes) -> bytes:
        """
        Decodes a null-terminated byte sequence (excluding the null terminator)
        back into the original byte sequence, handling escapes.
        """
        pass

    @abstractmethod
    def encode_integer(self, value: int) -> bytes:
        """
        Encodes a positive integer as a null-terminated byte sequence.
        First to big-endian bytes, then encoded.
        """
        pass

    @abstractmethod
    def decode_integer(self, data: bytes) -> int:
        """
        Decodes a null-terminated byte sequence into an integer.
        """
        pass

    @abstractmethod
    def encode_sequence_list(self, sequences: List[bytes]) -> bytes:
        """
        Encodes a list of null-terminated byte sequences into a single
        null-terminated byte sequence.
        """
        pass

    @abstractmethod
    def decode_sequence_list(self, data: bytes) -> List[bytes]:
        """
        Decodes a single null-terminated byte sequence into a list of
        null-terminated byte sequences.
        """
        pass


class LowLevelIOABC(ABC):
    """
    Abstract Base Class for Low Level I/O module.
    Handles reading/writing repository files and caching byte sequences.
    """
    @abstractmethod
    def open_new_repository(self, filepath: str, version: int = 1) -> None:
        """
        Opens a new repository for writing.
        Initialises cache.
        Writes version number as first sequence.
        """
        pass

    @abstractmethod
    def open_existing_repository_read(self, filepath: str) -> None:
        """
        Opens an existing repository for reading.
        Reads and caches the entire repository.
        """
        pass

    @abstractmethod
    def open_existing_repository_append(self, filepath: str) -> None:
        """
        Opens an existing repository for appending.
        Must have been read first.
        Checks if file size matches the end of the cached data.
        Raises StaleCacheError (or similar) if file has changed.
        """
        pass

    @abstractmethod
    def close_repository(self) -> None:
        """
        Closes the repository file and release cache.
        """
        pass

    @abstractmethod
    def read_byte_sequence(self) -> Tuple[bytes, int]:
        """
        Reads the next null-terminated byte sequence from the file.
        Returns (decoded_bytes, sequence_number).
        """
        pass

    @abstractmethod
    def write_byte_sequence(self, data: bytes) -> int:
        """
        Writes a byte sequence to the repository if not already present.
        Returns the sequence number (new or existing).
        """
        pass

    @abstractmethod
    def get_sequence_number(self, data: bytes) -> Optional[int]:
        """
        Retrieves sequence number from cache by byte sequence.
        """
        pass

    @abstractmethod
    def get_byte_sequence(self, seq_num: int) -> bytes:
        """
        Retrieves byte sequence from cache by sequence number.
        """
        pass


class SExpressionsABC(ABC):
    """
    Abstract Base Class for S-Expressions module.
    """
    @abstractmethod
    def write_nil(self) -> int:
        """
        Writes Nil S-expression to repository.
        Returns sequence number.
        """
        pass

    @abstractmethod
    def write_atom(self, value: bytes) -> int:
        """
        Writes Atom S-expression to repository.
        Returns sequence number.
        """
        pass

    @abstractmethod
    def write_cons(self, car_seq_num: int, cdr_seq_num: int) -> int:
        """
        Writes CONS cell S-expression to repository.
        Returns sequence number.
        """
        pass

    @abstractmethod
    def read_sexpression(self, seq_num: int) -> Union[None, bytes, Tuple[int, int]]:
        """
        Reads S-expression from cache given sequence number.
        Returns None (Nil), bytes (Atom), or (car, cdr) tuple (Cons).
        """
        pass

    @abstractmethod
    def push_nil(self) -> None:
        """
        Writes Nil and pushes sequence number to stack.
        """
        pass

    @abstractmethod
    def push_atom(self, value: bytes) -> None:
        """
        Writes Atom and pushes sequence number to stack.
        """
        pass

    @abstractmethod
    def stack_cons(self) -> None:
        """
        Pops top two items, writes Cons, pushes result sequence number.
        """
        pass
