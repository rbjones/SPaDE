"""Tests for the reference-based Python T-expression repository layer."""

import os
import tempfile
import unittest
from unittest.mock import patch

from kr.krcd009 import EncodingDecoding, LowLevelIO
from kr.krcd014 import TExpression, TExpressions


class TestTExpressions(unittest.TestCase):
    def setUp(self):
        self.temp_dir = tempfile.TemporaryDirectory()
        self.path = os.path.join(self.temp_dir.name, "trees.spade")
        self.io = LowLevelIO()
        self.io.open_new_repository(self.path)
        self.trees = TExpressions(self.io)
        self.encoding = EncodingDecoding()

    def tearDown(self):
        self.io.close_repository()
        self.temp_dir.cleanup()

    def test_leaf_labels_and_record_layout(self):
        for label in (b"", b"leaf", b"\x00\x01\x02\x01\x00\x01"):
            with self.subTest(label=label):
                seq = self.trees.write_node(label, [])
                self.assertEqual(self.trees.read_node(seq), TExpression(label, []))
                self.assertEqual(
                    self.io.get_byte_sequence(seq), self.encoding.encode_sequence_list([label])
                )

    def test_nested_shared_children_and_reopen_append(self):
        leaf = self.trees.write_node(b"shared\x00\x01", [])
        other = self.trees.write_node(b"other", [])
        branch = self.trees.write_node(b"branch", [leaf, other, leaf])
        parent = self.trees.write_node(b"parent", [branch, leaf])
        records = [self.io.get_byte_sequence(n) for n in (leaf, other, branch, parent)]
        expected = self.encoding.encode_sequence_list([
            b"parent", self.encoding.encode_integer(branch), self.encoding.encode_integer(leaf)
        ])
        self.assertEqual(records[-1], expected)
        self.assertEqual(self.trees.read_node(branch), TExpression(b"branch", [leaf, other, leaf]))
        self.assertEqual(self.trees.read_node(parent), TExpression(b"parent", [branch, leaf]))

        self.io.close_repository()
        with open(self.path, "rb") as repository:
            before = repository.read()
        self.io.open_existing_repository_read(self.path)
        self.assertEqual(self.trees.read_node(leaf), TExpression(b"shared\x00\x01", []))
        self.assertEqual(self.trees.read_node(parent), TExpression(b"parent", [branch, leaf]))
        self.io.open_existing_repository_append(self.path)
        amendment = self.trees.write_node(b"amendment", [branch, leaf])
        self.assertEqual(amendment, parent + 1)
        self.assertEqual(self.trees.write_node(b"parent", [branch, leaf]), parent)
        self.assertEqual(
            [self.io.get_byte_sequence(n) for n in (leaf, other, branch, parent)], records
        )
        self.io.close_repository()
        with open(self.path, "rb") as repository:
            after = repository.read()
        amendment_record = self.encoding.encode_sequence_list([
            b"amendment", self.encoding.encode_integer(branch), self.encoding.encode_integer(leaf)
        ])
        self.assertEqual(after, before + self.encoding.encode_bytes(amendment_record))
        self.io.open_existing_repository_read(self.path)
        self.assertEqual(self.trees.read_node(amendment), TExpression(b"amendment", [branch, leaf]))

    def test_write_validates_shared_subtrees_once(self):
        leaf = self.trees.write_node(b"leaf", [])
        shared = self.trees.write_node(b"shared", [leaf])
        first = self.trees.write_node(b"first", [shared])
        second = self.trees.write_node(b"second", [shared])

        with patch.object(self.trees, "_read_record", wraps=self.trees._read_record) as read_record:
            parent = self.trees.write_node(b"parent", [first, second, first])

        validated = [call.args[0] for call in read_record.call_args_list]
        self.assertEqual(set(validated), {first, second, shared, leaf})
        self.assertEqual(len(validated), len(set(validated)))
        self.assertEqual(self.trees.read_node(parent).children, [first, second, first])

    def test_reference_encodings_cross_byte_boundary(self):
        nodes = [self.trees.write_node(str(i).encode(), []) for i in range(256)]
        parent = self.trees.write_node(b"parent", [nodes[0], nodes[254], nodes[255]])
        self.assertEqual(
            self.trees.read_node(parent), TExpression(b"parent", [nodes[0], nodes[254], nodes[255]])
        )
        self.assertEqual(self.io.get_byte_sequence(parent), self.encoding.encode_sequence_list([
            b"parent", b"\x01", b"\xff", b"\x01\x00"
        ]))

    def test_invalid_write_references(self):
        leaf = self.trees.write_node(b"leaf", [])
        for ref in (0, -1, leaf + 1, True, 1.5):
            with self.subTest(ref=ref), self.assertRaises(ValueError):
                self.trees.write_node(b"parent", [ref])
        with self.assertRaises(TypeError):
            self.trees.write_node("not bytes", [])
        malformed = self.io.write_byte_sequence(b"not terminated")
        with self.assertRaises(ValueError):
            self.trees.write_node(b"parent", [malformed])

    def test_malformed_records(self):
        leaf = self.trees.write_node(b"leaf", [])
        records = [
            b"", b"missing terminator", b"label\x00trailing", b"label\x00\x01",
            b"label\x00\x01\x00", b"label\x00\x00",
            self.encoding.encode_sequence_list([b"label", b"\x00"]),
            self.encoding.encode_sequence_list([b"label", b"\x00\x01"]),
            self.encoding.encode_sequence_list([b"label", b"\xff"]),
        ]
        for record in records:
            with self.subTest(record=record):
                seq = self.io.write_byte_sequence(record)
                with self.assertRaises(ValueError):
                    self.trees.read_node(seq)
        self_ref = self.encoding.encode_sequence_list([
            b"self", self.encoding.encode_integer(malformed_next := seq + 1)
        ])
        self.assertEqual(self.io.write_byte_sequence(self_ref), malformed_next)
        with self.assertRaises(ValueError):
            self.trees.read_node(malformed_next)
        self.assertEqual(self.trees.read_node(leaf), TExpression(b"leaf", []))

    def test_deduplicated_record_cannot_create_forward_reference(self):
        future = 2
        payload = self.encoding.encode_sequence_list([b"parent", b"\x02"])
        self.assertEqual(self.io.write_byte_sequence(payload), 1)
        self.assertEqual(self.trees.write_node(b"leaf", []), future)
        with self.assertRaises(ValueError):
            self.trees.write_node(b"parent", [future])

    def test_malformed_descendants_are_rejected(self):
        broken = self.io.write_byte_sequence(b"unterminated")
        branch = self.io.write_byte_sequence(
            self.encoding.encode_sequence_list([b"branch", self.encoding.encode_integer(broken)])
        )
        parent = self.io.write_byte_sequence(
            self.encoding.encode_sequence_list([b"parent", self.encoding.encode_integer(branch)])
        )
        with self.assertRaises(ValueError):
            self.trees.read_node(parent)
        with self.assertRaises(ValueError):
            self.trees.write_node(b"new", [branch])

    def test_version_collision_fails_explicitly(self):
        self.io.close_repository()
        self.io.open_new_repository(self.path, version=512)
        with self.assertRaisesRegex(ValueError, "collides"):
            self.trees.write_node(b"\x02", [])


if __name__ == "__main__":
    unittest.main()
