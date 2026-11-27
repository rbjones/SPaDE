"""T-expression nodes stored as labels and backward repository references."""

from dataclasses import dataclass
from typing import List, Optional

from kr.krcd008 import EncodingDecodingABC, LowLevelIOABC
from kr.krcd009 import EncodingDecoding


@dataclass
class TExpression:
    label: bytes
    children: List[int]


class TExpressions:
    """Store each node as NTBSS [label, child sequence number, ...].

    Sequence numbers use the existing minimal big-endian integer encoding.
    Sequence 0 is the repository version, not a node. Children must already
    be stored, and every reference must precede its parent.
    A node whose payload equals the version record cannot be stored because
    the low-level I/O deduplicates all byte sequences, including the version.
    """

    def __init__(self, io: LowLevelIOABC, encoding: Optional[EncodingDecodingABC] = None):
        self.io = io
        self.encoding = encoding or EncodingDecoding()

    def write_node(self, label: bytes, children: List[int]) -> int:
        if not isinstance(label, bytes):
            raise TypeError("Node label must be bytes")

        child_bytes = []
        for child in children:
            self.read_node(child)
            child_bytes.append(self.encoding.encode_integer(child))

        payload = self.encoding.encode_sequence_list([label] + child_bytes)
        existing = self.io.get_sequence_number(payload)
        if existing == 0:
            raise ValueError("Node record collides with the repository version")
        if existing is not None and any(child >= existing for child in children):
            raise ValueError("Child reference must precede its parent")
        return self.io.write_byte_sequence(payload)

    def read_node(self, seq_num: int) -> TExpression:
        if type(seq_num) is not int or seq_num <= 0:
            raise ValueError("Node sequence number must be a positive integer")
        node = self._read_record(seq_num)
        pending = list(node.children)
        seen = set()
        while pending:
            child = pending.pop()
            if child not in seen:
                seen.add(child)
                pending.extend(self._read_record(child).children)
        return node

    def _read_record(self, seq_num: int) -> TExpression:
        try:
            payload = self.io.get_byte_sequence(seq_num)
        except IndexError as exc:
            raise ValueError("Node sequence number does not exist") from exc

        # The underlying list decoder ignores unterminated trailing data.
        i = 0
        terminated = False
        while i < len(payload):
            byte = payload[i]
            i += 2 if byte == 1 else 1
            terminated = byte == 0
        if not terminated or i > len(payload):
            raise ValueError("Unterminated T-expression record")

        parts = self.encoding.decode_sequence_list(payload)
        if not parts:
            raise ValueError("T-expression record is missing its label")
        children = []
        for part in parts[1:]:
            child = self.encoding.decode_integer(part)
            if not part or part != self.encoding.encode_integer(child):
                raise ValueError("Invalid child sequence number encoding")
            if child <= 0 or child >= seq_num:
                raise ValueError("Child reference must be a backward node reference")
            children.append(child)
        return TExpression(parts[0], children)
