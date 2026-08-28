(* Extended SML tests for the krcd011 structures. *)

exception TestFail of string;

fun assert_bool (label, true) = ()
  | assert_bool (label, false) = raise TestFail ("Assertion failed: " ^ label);

fun assert_int (label, expected, actual) =
    assert_bool (label ^ " (expected " ^ Int.toString expected ^ ", got " ^ Int.toString actual ^ ")",
                 expected = actual);

fun assert_vec (label, expected: Word8Vector.vector, actual) =
    assert_bool (label, Word8Vector.equals (expected, actual));

fun assert_vec_list (label, expected, actual) =
    let
        fun loop ([], []) = ()
          | loop (e :: es, a :: as) = (assert_vec (label, e, a); loop (es, as))
          | loop _ = raise TestFail ("Length mismatch in " ^ label)
    in loop (expected, actual) end

fun expect_fail_msg (label, expected, thunk) =
    (thunk (); raise TestFail (label ^ " expected failure"))
    handle TestFail msg => if msg = expected then () else raise TestFail (label ^ " wrong message: " ^ msg)

fun expect_stale (label, thunk) =
    (thunk (); raise TestFail (label ^ " expected stale cache error"))
    handle LowLevelIO.StaleCacheError _ => ()

(* Encoding/decoding tests *)
val _ = (
    let
        val raw = Word8Vector.fromList [0w0, 0w1, 0w2]
        val escaped = Word8Vector.fromList [0w1, 0w0, 0w1, 0w1, 0w2, 0w0]
        val encoded = EncodingDecoding.encode_bytes raw
        val _ = assert_vec ("encode_bytes escapes", escaped, encoded)
        val _ = assert_vec ("decode_bytes roundtrip", raw, EncodingDecoding.decode_bytes (Word8Vector.fromList [0w1, 0w0, 0w1, 0w1, 0w2]))
        val _ = expect_fail_msg ("decode_bytes EOF", "Unexpected EOF after escape",
                                 fn () => EncodingDecoding.decode_bytes (Word8Vector.fromList [0w1]))

        val ints = [(0, Word8Vector.fromList [0w0]), (1, Word8Vector.fromList [0w1]),
                    (255, Word8Vector.fromList [0w255]), (256, Word8Vector.fromList [0w1, 0w0])]
        val _ = List.app (fn (n, bytes) => (assert_vec ("encode_integer", bytes, EncodingDecoding.encode_integer n);
                                            assert_int ("decode_integer", n, EncodingDecoding.decode_integer bytes))) ints

        val seqs1 = [Word8Vector.fromList [0w65], Word8Vector.fromList [0w66]]
        val enc_list1 = EncodingDecoding.encode_sequence_list seqs1
        val _ = assert_vec ("encode_sequence_list simple", Word8Vector.fromList [0w65, 0w0, 0w66, 0w0], enc_list1)
        val _ = assert_vec_list ("decode_sequence_list simple", seqs1, EncodingDecoding.decode_sequence_list enc_list1)

        val seqs2 = [Word8Vector.fromList [0w0], Word8Vector.fromList [0w1]]
        val enc_list2 = EncodingDecoding.encode_sequence_list seqs2
        val _ = assert_vec ("encode_sequence_list escaped", Word8Vector.fromList [0w1, 0w0, 0w0, 0w1, 0w1, 0w0], enc_list2)
        val _ = assert_vec_list ("decode_sequence_list escaped", seqs2, EncodingDecoding.decode_sequence_list enc_list2)

        val _ = expect_fail_msg ("decode_sequence_list EOF", "Unexpected EOF after escape",
                                 fn () => EncodingDecoding.decode_sequence_list (Word8Vector.fromList [0w1]))
    in () end)

(* Low-level I/O tests *)
val repo_path = OS.FileSys.tmpName ()
val _ = (
    let
        val _ = LowLevelIO.open_new_repository (repo_path, 1)
        val version = LowLevelIO.get_byte_sequence 0
        val _ = assert_vec ("version payload", Word8Vector.fromList [0w1], version)

        val hello = Word8Vector.fromList (map Word8.fromInt [72, 101, 108, 108, 111])
        val seq_hello = LowLevelIO.write_byte_sequence hello
        val _ = assert_int ("hello seq", 1, seq_hello)

        val zeros = Word8Vector.fromList [0w0]
        val seq_zero = LowLevelIO.write_byte_sequence zeros
        val _ = assert_int ("zero seq", 2, seq_zero)

        val _ = assert_vec ("get hello", hello, LowLevelIO.get_byte_sequence seq_hello)
        val _ = assert_vec ("get zero", zeros, LowLevelIO.get_byte_sequence seq_zero)
        val _ = assert_bool ("sequence reuse", LowLevelIO.write_byte_sequence hello = seq_hello)
        val _ = assert_bool ("get_sequence_number SOME", LowLevelIO.get_sequence_number hello = SOME seq_hello)
        val _ = LowLevelIO.close_repository ()

        val _ = LowLevelIO.open_existing_repository_read repo_path
        val _ = assert_vec ("persist version", Word8Vector.fromList [0w1], LowLevelIO.get_byte_sequence 0)
        val _ = assert_vec ("persist hello", hello, LowLevelIO.get_byte_sequence 1)
        val _ = assert_vec ("persist zero", zeros, LowLevelIO.get_byte_sequence 2)

        (* Stale cache detection *)
        val _ = (
            let
                val out = BinIO.openAppend repo_path
                val _ = BinIO.output1 (out, 0w7)
                val _ = BinIO.closeOut out
            in expect_stale ("stale cache", fn () => LowLevelIO.open_existing_repository_append repo_path) end)
        val _ = LowLevelIO.close_repository ()
    in () end)

(* S-expression tests *)
val sexp_repo = OS.FileSys.tmpName ()
val _ = (
    let
        val _ = LowLevelIO.open_new_repository (sexp_repo, 1)
        val _ = (SExpressions.stack := [])

        val nil_seq = SExpressions.write_nil ()
        val _ = (case SExpressions.read_sexpression nil_seq of SExpressions.Nil => () | _ => raise TestFail "nil roundtrip")

        val atom_bytes = Word8Vector.fromList [0w65, 0w0]
        val atom_seq = SExpressions.write_atom atom_bytes
        val _ = (case SExpressions.read_sexpression atom_seq of
                    SExpressions.Atom v => assert_vec ("atom roundtrip", atom_bytes, v)
                  | _ => raise TestFail "atom roundtrip")

        val cons_seq = SExpressions.write_cons (atom_seq, nil_seq)
        val _ = (case SExpressions.read_sexpression cons_seq of
                    SExpressions.Cons (car, cdr) => (assert_int ("cons car", atom_seq, car);
                                                     assert_int ("cons cdr", nil_seq, cdr))
                  | _ => raise TestFail "cons roundtrip")

        val _ = (SExpressions.stack := []);
        val _ = SExpressions.push_atom atom_bytes;
        val _ = SExpressions.push_atom (Word8Vector.fromList [0w66]);
        val _ = SExpressions.stack_cons ();
        val _ = assert_int ("stack length", 1, length (!SExpressions.stack));
        val stack_cons_seq = hd (!SExpressions.stack);
        val _ = (case SExpressions.read_sexpression stack_cons_seq of
                    SExpressions.Cons (car, cdr) => (assert_vec ("stack car", atom_bytes, LowLevelIO.get_byte_sequence car);
                                                     assert_vec ("stack cdr", Word8Vector.fromList [0w66], LowLevelIO.get_byte_sequence cdr))
                  | _ => raise TestFail "stack cons");

        val list_value = SExpressions.ConsValue (SExpressions.AtomValue atom_bytes,
                        SExpressions.ConsValue (SExpressions.AtomValue (Word8Vector.fromList [0w66]), SExpressions.NilValue));
        val list_seq = SExpressions.write_recursive list_value;
        val _ = (case SExpressions.read_recursive list_seq of
                    SExpressions.ConsValue (SExpressions.AtomValue a,
                        SExpressions.ConsValue (SExpressions.AtomValue b, SExpressions.NilValue)) =>
                            (assert_vec ("recursive a", atom_bytes, a);
                             assert_vec ("recursive b", Word8Vector.fromList [0w66], b))
                  | _ => raise TestFail "recursive roundtrip");

        (* Error cases *)
        val empty_seq = LowLevelIO.write_byte_sequence (SExpressions.encoding.encode_sequence_list []);
        val _ = expect_fail_msg ("empty payload", "Empty S-expression payload",
                                 fn () => SExpressions.read_sexpression empty_seq);

        val atom_only = LowLevelIO.write_byte_sequence (SExpressions.encoding.encode_sequence_list [Word8Vector.fromList [0w3]]);
        val _ = expect_fail_msg ("atom missing value", "Atom missing value",
                                 fn () => SExpressions.read_sexpression atom_only);

        val cons_missing = LowLevelIO.write_byte_sequence (SExpressions.encoding.encode_sequence_list [Word8Vector.fromList [0w4], Word8Vector.fromList [0w0]])
        val _ = expect_fail_msg ("cons missing", "Cons missing pointers",
                                 fn () => SExpressions.read_sexpression cons_missing);

        val unknown_tag = LowLevelIO.write_byte_sequence (SExpressions.encoding.encode_sequence_list [Word8Vector.fromList [0w5]])
        val _ = expect_fail_msg ("unknown tag", "Unknown S-expression type",
                                 fn () => SExpressions.read_sexpression unknown_tag)

        val _ = (SExpressions.stack := []);
        val _ = expect_fail_msg ("stack underflow", "Stack underflow", fn () => SExpressions.stack_cons ())

        val _ = LowLevelIO.close_repository ()
    in () end);

val _ = (OS.FileSys.remove repo_path handle _ => ();
         OS.FileSys.remove sexp_repo handle _ => ();
         print "krte006: tests passed\n");
