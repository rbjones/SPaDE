(* Minimal SML unit test for repository encoding and S-expression roundtrips. *)

fun assert_bool (msg, true) = ()
    | assert_bool (msg, false) = raise Fail ("Assertion failed: " ^ msg)

fun assert_int (msg, a, b) = assert_bool (msg, a = b)

fun assert_bytes (msg, a:Word8Vector.vector, b) =
        assert_bool (msg, Word8Vector.equals (a, b))

val _ = LowLevelIO.open_new_repository ("/tmp/spade-test.repo", 1)

val bytes1 = Word8Vector.fromList [0w10,0w20,0w0,0w30]
val bytes2 = Word8Vector.fromList [0w40,0w1,0w2]

val seq_a = LowLevelIO.write_byte_sequence bytes1
val seq_b = LowLevelIO.write_byte_sequence bytes2
val seq_a_again = LowLevelIO.write_byte_sequence bytes1

val _ = assert_int ("sequence reuse", seq_a, seq_a_again)
val _ = assert_bytes ("payload a", bytes1, LowLevelIO.get_byte_sequence seq_a)
val _ = assert_bytes ("payload b", bytes2, LowLevelIO.get_byte_sequence seq_b)

val sexp_nil = SExpressions.write_nil ()
val sexp_atom = SExpressions.write_atom bytes1
val sexp_cons = SExpressions.write_cons (sexp_atom, sexp_nil)

val _ = (case SExpressions.read_sexpression sexp_nil of
            SExpressions.Nil => ()
        | _ => raise Fail "Nil roundtrip failed")

val _ = (case SExpressions.read_sexpression sexp_atom of
            SExpressions.Atom v => assert_bytes ("atom roundtrip", bytes1, v)
        | _ => raise Fail "Atom roundtrip failed")

val _ = (case SExpressions.read_sexpression sexp_cons of
            SExpressions.Cons (car,cdr) =>
                (assert_int ("car ptr", sexp_atom, car);
                    assert_int ("cdr ptr", sexp_nil, cdr))
        | _ => raise Fail "Cons roundtrip failed")

val recursive_in = SExpressions.ConsValue (SExpressions.AtomValue bytes2, SExpressions.NilValue)
val recursive_seq = SExpressions.write_recursive recursive_in
val recursive_out = SExpressions.read_recursive recursive_seq

val _ = (case recursive_out of
            SExpressions.ConsValue (SExpressions.AtomValue v, SExpressions.NilValue) =>
                assert_bytes ("recursive atom payload", bytes2, v)
        | _ => raise Fail "Recursive roundtrip failed")

val _ = LowLevelIO.close_repository ()

(* Signal success to ProofPower/pp *)
val _ = print "krte004: tests passed\n"
