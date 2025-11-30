import unittest
import os
import tempfile
import shutil
from kr.krcd009 import EncodingDecoding, LowLevelIO, SExpressions, StaleCacheError

class TestEncodingDecoding(unittest.TestCase):
    def setUp(self):
        self.ed = EncodingDecoding()

    def test_escape_unescape(self):
        # Test cases: (raw, escaped_content)
        # Note: encode_bytes adds \0 at end, so we check that separately or strip it
        cases = [
            (b'hello', b'hello'),
            (b'\x00', b'\x01\x00'),
            (b'\x01', b'\x01\x01'),
            (b'\x00\x01', b'\x01\x00\x01\x01'),
            (b'a\x00b\x01c', b'a\x01\x00b\x01c'),
            # New optimization tests
            (b'\x01\x02', b'\x01\x02'), # 1 followed by 2 -> no escape
            (b'\x01\x00', b'\x01\x01\x01\x00'), # 1 followed by 0 -> escape 1, escape 0
            (b'\x01\x01', b'\x01\x01\x01\x01'), # 1 followed by 1 -> escape 1, escape 1
        ]
        for raw, expected_content in cases:
            encoded = self.ed.encode_bytes(raw)
            self.assertEqual(encoded, expected_content + b'\x00')
            
            decoded = self.ed.decode_bytes(expected_content)
            self.assertEqual(decoded, raw)

    def test_unescape_errors(self):
        # Unexpected end of data after escape
        with self.assertRaises(ValueError):
            self.ed.decode_bytes(b'\x01')

    def test_sequence_list_errors(self):
        # Unexpected end of data after escape in sequence list
        with self.assertRaises(ValueError):
            self.ed.decode_sequence_list(b'\x01')

    def test_integer_encoding(self):
        cases = [
            (0, b'\x00'),
            (1, b'\x01'),
            (255, b'\xff'),
            (256, b'\x01\x00'),
        ]
        for val, expected in cases:
            encoded = self.ed.encode_integer(val)
            self.assertEqual(encoded, expected)
            decoded = self.ed.decode_integer(encoded)
            self.assertEqual(decoded, val)

    def test_sequence_list(self):
        # List of [b'A', b'B']
        # NTBS(A) = b'A\0'
        # NTBS(B) = b'B\0'
        # Concat = b'A\0B\0'
        # Encoded = Escape(Concat) + \0
        # Escape(A\0B\0) = A \1\0 B \1\0
        
        seqs = [b'A', b'B']
        encoded_list = self.ed.encode_sequence_list(seqs)
        # Expected: b'A\x01\x00B\x01\x00' (Note: encode_sequence_list returns payload, not NTBS wrapped)
        # Wait, encode_sequence_list calls encode_bytes for each item.
        # encode_bytes(A) -> A\0.
        # encode_bytes(B) -> B\0.
        # Result is concatenation.
        # So result is b'A\x00B\x00'.
        # Wait, my implementation of encode_sequence_list:
        # out.extend(self.encode_bytes(seq))
        # encode_bytes returns escaped + \0.
        # So yes, b'A\0B\0'.
        
        # BUT, LowLevelIO will escape this result when writing.
        # So if I pass this to decode_sequence_list, it expects the payload (b'A\0B\0').
        
        self.assertEqual(encoded_list, b'A\x00B\x00')
        decoded = self.ed.decode_sequence_list(encoded_list)
        self.assertEqual(decoded, seqs)
        
        # Test with special chars
        seqs = [b'\x00', b'\x01']
        # encode_bytes(b'\x00') -> b'\x01\x00\x00'
        # encode_bytes(b'\x01') -> b'\x01\x01\x00'
        # Concat: b'\x01\x00\x00\x01\x01\x00'
        encoded_list = self.ed.encode_sequence_list(seqs)
        self.assertEqual(encoded_list, b'\x01\x00\x00\x01\x01\x00')
        decoded = self.ed.decode_sequence_list(encoded_list)
        self.assertEqual(decoded, seqs)


class TestLowLevelIO(unittest.TestCase):
    def setUp(self):
        self.temp_dir = tempfile.mkdtemp()
        self.repo_path = os.path.join(self.temp_dir, 'test.spade')
        self.io = LowLevelIO()

    def tearDown(self):
        self.io.close_repository()
        shutil.rmtree(self.temp_dir)

    def test_new_repo(self):
        self.io.open_new_repository(self.repo_path, version=1)
        self.io.close_repository()
        
        self.assertTrue(os.path.exists(self.repo_path))
        
        # Check content: Version 1 encoded.
        # 1 -> b'\x01'.
        # NTBS(b'\x01') -> b'\x01\x01\x00'. (1 escapes to 1 1).
        with open(self.repo_path, 'rb') as f:
            content = f.read()
        self.assertEqual(content, b'\x01\x01\x00')

    def test_write_read(self):
        self.io.open_new_repository(self.repo_path)
        # Seq 0 is version (1)
        
        # Write b'hello'
        seq_num = self.io.write_byte_sequence(b'hello')
        self.assertEqual(seq_num, 1)
        
        # Write b'\x00'
        seq_num2 = self.io.write_byte_sequence(b'\x00')
        self.assertEqual(seq_num2, 2)
        
        self.io.close_repository()
        
        # Read back
        self.io.open_existing_repository_read(self.repo_path)
        
        # Seq 0
        val0 = self.io.get_byte_sequence(0)
        self.assertEqual(val0, b'\x01') # Version 1
        
        # Seq 1
        val1 = self.io.get_byte_sequence(1)
        self.assertEqual(val1, b'hello')
        
        # Seq 2
        val2 = self.io.get_byte_sequence(2)
        self.assertEqual(val2, b'\x00')

    def test_deduplication(self):
        self.io.open_new_repository(self.repo_path)
        s1 = self.io.write_byte_sequence(b'A')
        s2 = self.io.write_byte_sequence(b'A')
        self.assertEqual(s1, s2)
        self.io.close_repository()

    def test_append_stale_cache(self):
        self.io.open_new_repository(self.repo_path)
        self.io.write_byte_sequence(b'A')
        self.io.close_repository()
        
        # Open read
        self.io.open_existing_repository_read(self.repo_path)
        
        # Modify file externally
        with open(self.repo_path, 'ab') as f:
            f.write(b'junk')
            
        # Try append
        with self.assertRaises(StaleCacheError):
            self.io.open_existing_repository_append(self.repo_path)

    def test_io_errors(self):
        # Test read when not open
        with self.assertRaises(ValueError):
            self.io.read_byte_sequence()
            
        # Test write when not open
        with self.assertRaises(ValueError):
            self.io.write_byte_sequence(b'foo')
            
        # Test append without read
        self.io.open_new_repository(self.repo_path)
        self.io.close_repository()
        # Reset mode
        self.io._mode = None
        with self.assertRaises(ValueError):
            self.io.open_existing_repository_append(self.repo_path)

    def test_read_corrupt_file(self):
        # Create file with EOF after escape
        with open(self.repo_path, 'wb') as f:
            f.write(b'\x01') # Escape char then EOF
            
        with self.assertRaises(ValueError):
            self.io.open_existing_repository_read(self.repo_path)


class TestSExpressions(unittest.TestCase):
    def setUp(self):
        self.temp_dir = tempfile.mkdtemp()
        self.repo_path = os.path.join(self.temp_dir, 'sexpr.spade')
        self.io = LowLevelIO()
        self.io.open_new_repository(self.repo_path)
        self.sexp = SExpressions(self.io)

    def tearDown(self):
        self.io.close_repository()
        shutil.rmtree(self.temp_dir)

    def test_nil(self):
        seq = self.sexp.write_nil()
        # Read back
        val = self.sexp.read_sexpression(seq)
        self.assertIsNone(val)

    def test_atom(self):
        seq = self.sexp.write_atom(b'foo')
        val = self.sexp.read_sexpression(seq)
        self.assertEqual(val, b'foo')

    def test_cons(self):
        # Create two atoms
        a1 = self.sexp.write_atom(b'A')
        a2 = self.sexp.write_atom(b'B')
        
        # Cons them
        c = self.sexp.write_cons(a1, a2)
        
        val = self.sexp.read_sexpression(c)
        self.assertEqual(val, (a1, a2))

    def test_stack(self):
        self.sexp.push_atom(b'A')
        self.sexp.push_atom(b'B')
        self.sexp.stack_cons()
        
        # Stack should have 1 item (the cons)
        self.assertEqual(len(self.sexp.stack), 1)
        cons_seq = self.sexp.stack[0]
        
        val = self.sexp.read_sexpression(cons_seq)
        # Cons(A, B). A is car, B is cdr.
        # Stack was [A, B].
        # stack_cons pops top (B) as cdr, then next (A) as car.
        # So Cons(A, B).
        
        self.assertIsInstance(val, tuple)
        # Verify A and B seq nums
        # We don't know exact seq nums easily without tracking, but we can read them recursively
        car_seq, cdr_seq = val
        car_val = self.sexp.read_sexpression(car_seq)
        cdr_val = self.sexp.read_sexpression(cdr_seq)
        
        self.assertEqual(car_val, b'A')
        self.assertEqual(cdr_val, b'B')

    def test_recursive(self):
        # Test list [A, B] -> (A . (B . Nil))
        data = [b'A', b'B']
        seq = self.sexp.write_recursive(data)
        
        val = self.sexp.read_recursive(seq)
        # Expected: (b'A', (b'B', None))
        self.assertEqual(val, (b'A', (b'B', None)))
        
        # Test nested: [A, [B, C]] -> (A . ((B . (C . Nil)) . Nil))
        data2 = [b'A', [b'B', b'C']]
        seq2 = self.sexp.write_recursive(data2)
        val2 = self.sexp.read_recursive(seq2)
        self.assertEqual(val2, (b'A', ((b'B', (b'C', None)), None)))

    def test_sexp_errors(self):
        # Empty payload
        # Mock IO to return empty bytes
        # We can't easily mock IO without subclassing or mocking, 
        # but we can write a raw sequence that is invalid S-Exp
        
        # 1. Empty payload
        # write_byte_sequence returns seq_num.
        # We can manually write bytes to IO.
        empty_seq = self.io.write_byte_sequence(self.sexp.encoding.encode_sequence_list([]))
        # Wait, encode_sequence_list([]) returns b''.
        # write_byte_sequence(b'') -> writes b'\x00' (escaped empty + null).
        # read_byte_sequence -> returns b''.
        # read_sexpression(seq) -> decode_sequence_list(b'') -> [].
        # parts = []. Raises ValueError "Empty S-expression payload".
        with self.assertRaisesRegex(ValueError, "Empty S-expression payload"):
            self.sexp.read_sexpression(empty_seq)
            
        # 2. Atom missing value
        # Atom type is \x03. Payload: [\x03].
        atom_incomplete = self.io.write_byte_sequence(self.sexp.encoding.encode_sequence_list([b'\x03']))
        with self.assertRaisesRegex(ValueError, "Atom missing value"):
            self.sexp.read_sexpression(atom_incomplete)
            
        # 3. Cons missing pointers
        # Cons type \x04. Payload: [\x04, car]. Missing cdr.
        cons_incomplete = self.io.write_byte_sequence(self.sexp.encoding.encode_sequence_list([b'\x04', b'\x00']))
        with self.assertRaisesRegex(ValueError, "Cons missing pointers"):
            self.sexp.read_sexpression(cons_incomplete)
            
        # 4. Unknown type
        # Type \x05
        unknown_type = self.io.write_byte_sequence(self.sexp.encoding.encode_sequence_list([b'\x05']))
        with self.assertRaisesRegex(ValueError, "Unknown S-expression type"):
            self.sexp.read_sexpression(unknown_type)

    def test_recursive_errors(self):
        # Unsupported type for write
        with self.assertRaisesRegex(TypeError, "Unsupported type"):
            self.sexp.write_recursive(123) # int not supported directly
            
        # Tuple wrong length
        with self.assertRaisesRegex(ValueError, "Tuple must be length 2"):
            self.sexp.write_recursive((1, 2, 3))

    def test_stack_errors(self):
        # Stack underflow
        self.sexp.stack = []
        with self.assertRaisesRegex(IndexError, "Stack underflow"):
            self.sexp.stack_cons()

if __name__ == '__main__':
    unittest.main()
