exception SimpleFail of string

structure EncodingDecoding =
struct
    type byte_sequence = Word8Vector.vector

    fun append_byte (v, b) = Word8Vector.concat [v, Word8Vector.fromList [b]]

    fun encode_bytes data =
            let
                fun esc b =
                        if b = 0w0 then [0w1, 0w0]
                        else if b = 0w1 then [0w1, 0w1]
                            else [b]
                val out = Word8Vector.concat (map (fn b => Word8Vector.fromList (esc b))
                        (Word8Vector.foldr op:: [] data))
            in
                append_byte(out, 0w0)
            end

    fun decode_bytes data =
            let
                fun step ([], acc) = rev acc
                    | step (0w1 :: xs, acc) =
                        (case xs of
                                [] => raise SimpleFail "Unexpected EOF after escape"
                            | 0w0 :: tl => step (tl, 0w0 :: acc)
                            | 0w1 :: tl => step (tl, 0w1 :: acc)
                            | b :: tl => step (tl, b :: 0w1 :: acc))
                    | step (0w0 :: tl, acc) = rev acc
                    | step (b :: tl, acc) = step (tl, b :: acc)
            in
                Word8Vector.fromList (step (Word8Vector.foldr op:: [] data, []))
            end

    fun encode_integer n =
            if n < 0 then raise SimpleFail "encode_integer: negative"
            else if n = 0 then Word8Vector.fromList [0w0]
                else
                    let
                        fun bytes 0 acc = acc
                            | bytes k acc = bytes (k div 256) (Word8.fromInt (k mod 256) :: acc)
                    in
                        Word8Vector.fromList (bytes n [])
                    end

    fun decode_integer v =
            let
                fun fold (b, acc) = acc * 256 + Word8.toInt b
            in
                Word8Vector.foldl fold 0 v
            end

    fun encode_sequence_list seqs =
            Word8Vector.concat (map encode_bytes seqs)

    fun decode_sequence_list data =
            let
                fun split ([], current, acc) = rev (decode_bytes (Word8Vector.fromList (rev current)) :: acc)
                  | split (0w0 :: tl, current, acc) =
                        split (tl, [], decode_bytes (Word8Vector.fromList (rev current)) :: acc)
                  | split (0w1 :: 0w0 :: tl, current, acc) = split (tl, 0w0 :: 0w1 :: current, acc)
                  | split (0w1 :: 0w1 :: tl, current, acc) = split (tl, 0w1 :: 0w1 :: current, acc)
                  | split (0w1 :: b :: tl, current, acc) = split (tl, b :: 0w1 :: current, acc)
                  | split (b :: tl, current, acc) = split (tl, b :: current, acc)
            in
                split (Word8Vector.foldr op:: [] data, [], [])
            end
end


structure LowLevelIO =
struct
    type byte_sequence = EncodingDecoding.byte_sequence
    type sequence_number = int

    exception StaleCacheError of string

    val filepath : string option ref = ref NONE
    val cache : byte_sequence list ref = ref []
    val cache_map : (byte_sequence * sequence_number) list ref = ref []
    val file_size : int ref = ref 0

    fun reset () = (filepath := NONE; cache := []; cache_map := []; file_size := 0)

    fun vec_equal (a: byte_sequence, b: byte_sequence) =
        let
            val la = Word8Vector.length a
            val lb = Word8Vector.length b
            fun loop i = i = la orelse (Word8Vector.sub (a, i) = Word8Vector.sub (b, i) andalso loop (i + 1))
        in la = lb andalso loop 0 end

    fun find_seq data =
            let
                fun loop [] = NONE
                    | loop ((d,n)::tl) = if vec_equal (d,data) then SOME n else loop tl
            in loop (!cache_map) end

    fun write_raw out bs = BinIO.output(out, bs)

    fun open_new_repository (path, version) =
            let
                val out = BinIO.openOut path
                val ver_bytes = EncodingDecoding.encode_bytes (EncodingDecoding.encode_integer version)
            in
                reset();
                filepath := SOME path;
                cache := [EncodingDecoding.encode_integer version];
                cache_map := [(hd(!cache),0)];
                file_size := Word8Vector.length ver_bytes;
                write_raw out ver_bytes;
                BinIO.closeOut out
            end

    fun read_all_bytes path =
            let
                val ins = BinIO.openIn path
                val data = BinIO.inputAll ins
                val _ = BinIO.closeIn ins
            in data end

    fun open_existing_repository_read path =
            let
                val data = read_all_bytes path
                val seqs = EncodingDecoding.decode_sequence_list data
            in
                reset();
                filepath := SOME path;
                cache := seqs;
                cache_map := ListPair.zip (seqs,
                    let fun tab n f =
                        let fun lp i acc = if i >= n then rev acc else lp (i+1) (f i :: acc)
                        in lp 0 [] end
                    in tab (length seqs) (fn i => i) end);
                file_size := Word8Vector.length data
            end

    fun open_existing_repository_append path =
            (case (!filepath, !cache) of
                    (SOME _, _) =>
                        let val size_on_disk = OS.FileSys.fileSize path
                        in if size_on_disk <> LargeInt.fromInt (!file_size) then
                            raise StaleCacheError "File changed on disk"
                            else () end
                    | _ => raise StaleCacheError "Must read repository before append")

    fun close_repository () = reset()

        fun read_byte_sequence () =
            raise StaleCacheError "read_byte_sequence: use open_existing_repository_read instead"

    fun write_byte_sequence data =
            case find_seq data of
                SOME n => n
            | NONE =>
                let
                    val seq_num = length (!cache)
                    val enc = EncodingDecoding.encode_bytes data
                    val _ = (case !filepath of
                                SOME path => let val out = BinIO.openAppend path
                                    in write_raw out enc; BinIO.closeOut out end
                            | NONE => ())
                in
                    cache := (!cache) @ [data];
                    cache_map := (!cache_map) @ [(data, seq_num)];
                    file_size := (!file_size) + Word8Vector.length enc;
                    seq_num
                end

        fun get_sequence_number data = find_seq data
        fun get_byte_sequence n =
            let fun nth (xs, k) =
                (case xs of
                    [] => raise Subscript
                  | x::tl => if k = 0 then x else nth (tl, k-1))
            in nth (!cache, n) end
end


structure SExpressions =
struct
    type byte_sequence = LowLevelIO.byte_sequence
    type sequence_number = LowLevelIO.sequence_number

    datatype sexp = Nil | Atom of byte_sequence | Cons of sequence_number * sequence_number
    datatype sexp_value =
        NilValue
    | AtomValue of byte_sequence
    | ConsValue of sexp_value * sexp_value

    fun write_nil () =
            LowLevelIO.write_byte_sequence (EncodingDecoding.encode_sequence_list [Word8Vector.fromList [0w2]])

    fun write_atom v =
            LowLevelIO.write_byte_sequence (EncodingDecoding.encode_sequence_list [Word8Vector.fromList [0w3], v])

    fun write_cons (car_seq, cdr_seq) =
            let
                val car_bytes = EncodingDecoding.encode_integer car_seq
                val cdr_bytes = EncodingDecoding.encode_integer cdr_seq
            in
                LowLevelIO.write_byte_sequence (EncodingDecoding.encode_sequence_list [Word8Vector.fromList [0w4], car_bytes, cdr_bytes])
            end

    fun read_sexpression seq_num =
            let
                val raw = LowLevelIO.get_byte_sequence seq_num
                val parts = EncodingDecoding.decode_sequence_list raw
            in
                case parts of
                    [] => raise SimpleFail "Empty S-expression payload"
                | tag :: rest =>
                    if tag = Word8Vector.fromList [0w2] then Nil
                    else if tag = Word8Vector.fromList [0w3] then
                            (case rest of
                                    v :: _ => Atom v
                                | _ => raise SimpleFail "Atom missing value")
                        else if tag = Word8Vector.fromList [0w4] then
                                (case rest of
                                        carb :: cdrb :: _ => Cons (EncodingDecoding.decode_integer carb, EncodingDecoding.decode_integer cdrb)
                                    | _ => raise SimpleFail "Cons missing pointers")
                                else raise SimpleFail "Unknown S-expression type"
            end

    val stack : sequence_number list ref = ref []

    fun push_nil () = stack := write_nil() :: (!stack)
    fun push_atom v = stack := write_atom v :: (!stack)

    fun stack_cons () =
            (case !stack of
                    cdr :: car :: rest => stack := write_cons (car, cdr) :: rest
                | _ => raise SimpleFail "Stack underflow")

    fun write_recursive NilValue = write_nil()
        | write_recursive (AtomValue v) = write_atom v
        | write_recursive (ConsValue (car, cdr)) =
            let val car_seq = write_recursive car
                val cdr_seq = write_recursive cdr
            in write_cons (car_seq, cdr_seq) end

    fun read_recursive seq =
            case read_sexpression seq of
                Nil => NilValue
            | Atom v => AtomValue v
            | Cons (car, cdr) => ConsValue (read_recursive car, read_recursive cdr)
end

(*
   Native service loop for driving the SML implementation from an external
   controller (e.g. Python). Commands are newline-terminated strings; results
   are single-line replies beginning OK/ERR followed by payload. Payloads that
   represent byte sequences are hex-encoded to keep the protocol ASCII-only.
*)
structure NativeRepoService =
struct
    (* hex helpers *)
    fun hex_of_word8 w =
        let
            val n = Word8.toInt w
            val hi = n div 16
            val lo = n mod 16
            fun nib x = if x < 10 then chr (x + ord "0")
                        else chr (x - 10 + ord "a")
        in nib hi ^ nib lo end

    fun hex_of_vec v =
        String.concat (map hex_of_word8 (Word8Vector.foldr op:: [] v))

    fun word8_of_hex2 s =
        let
            fun valof c =
                if c >= #"0" andalso c <= #"9" then ord (str c) - ord "0"
                else if c >= #"a" andalso c <= #"f" then 10 + ord (str c) - ord "a"
                else if c >= #"A" andalso c <= #"F" then 10 + ord (str c) - ord "A"
                else raise SimpleFail "bad hex"
        in
                                case String.explode s of
                                        [h1,h2] => Word8.fromInt (valof h1 * 16 + valof h2)
                                    | _ => raise SimpleFail "bad hex width"
        end

    fun vec_of_hex s =
        let
            val chars = String.size s
            fun loop i acc =
                if i >= chars then Word8Vector.fromList (rev acc)
                else loop (i+2) (word8_of_hex2 (String.extract (s, i, SOME 2)) :: acc)
        in
            if chars mod 2 <> 0 then raise SimpleFail "hex length not even" else loop 0 []
        end

    (* helpers to print replies *)
    fun ok payload = (TextIO.print ("OK " ^ payload ^ "\n"); TextIO.flushOut TextIO.stdOut)
    fun err msg = (TextIO.print ("ERR " ^ msg ^ "\n"); TextIO.flushOut TextIO.stdOut)

        (* command handlers *)
        fun dispatch ["ENCODE_BYTES", hex] = ok (hex_of_vec (EncodingDecoding.encode_bytes (vec_of_hex hex)))
            | dispatch ["DECODE_BYTES", hex] = ok (hex_of_vec (EncodingDecoding.decode_bytes (vec_of_hex hex)))
            | dispatch ["ENCODE_INT", n] = ok (hex_of_vec (EncodingDecoding.encode_integer (valOf (Int.fromString n))))
            | dispatch ["DECODE_INT", hex] = ok (Int.toString (EncodingDecoding.decode_integer (vec_of_hex hex)))
        | dispatch ["DECODE_SEQ_LIST", hex] =
        let
            val parts = EncodingDecoding.decode_sequence_list (vec_of_hex hex)
            val out = String.concatWith "," (map hex_of_vec parts)
        in ok out end

            | dispatch ["OPEN_NEW", path, ver] = (LowLevelIO.open_new_repository (path, valOf (Int.fromString ver)); ok "")
            | dispatch ["OPEN_READ", path] = (LowLevelIO.open_existing_repository_read path; ok "")
            | dispatch ["OPEN_APPEND", path] = (LowLevelIO.open_existing_repository_append path; ok "")
            | dispatch ["CLOSE"] = (LowLevelIO.close_repository(); ok "")

            | dispatch ["READ_BSEQ"] =
            let val (bs, n) = LowLevelIO.read_byte_sequence()
            in ok (Int.toString n ^ " " ^ hex_of_vec bs) end

            | dispatch ["WRITE_BSEQ", hex] = ok (Int.toString (LowLevelIO.write_byte_sequence (vec_of_hex hex)))
            | dispatch ["GET_SEQ", hex] = (case LowLevelIO.get_sequence_number (vec_of_hex hex) of
                                        SOME n => ok (Int.toString n)
                                      | NONE => ok "NONE")
            | dispatch ["GET_BSEQ", n] = ok (hex_of_vec (LowLevelIO.get_byte_sequence (valOf (Int.fromString n))))

            | dispatch ["WRITE_NIL"] = ok (Int.toString (SExpressions.write_nil()))
            | dispatch ["WRITE_ATOM", hex] = ok (Int.toString (SExpressions.write_atom (vec_of_hex hex)))
            | dispatch ["WRITE_CONS", car, cdr] = ok (Int.toString (SExpressions.write_cons (valOf (Int.fromString car), valOf (Int.fromString cdr))))
            | dispatch ["READ_SEXP", n] =
            (case SExpressions.read_sexpression (valOf (Int.fromString n)) of
                SExpressions.Nil => ok "NIL"
              | SExpressions.Atom v => ok ("ATOM " ^ hex_of_vec v)
              | SExpressions.Cons (a,b) => ok ("CONS " ^ Int.toString a ^ " " ^ Int.toString b))
            | dispatch ["PUSH_NIL"] = (SExpressions.push_nil(); ok "")
            | dispatch ["PUSH_ATOM", hex] = (SExpressions.push_atom (vec_of_hex hex); ok "")
            | dispatch ["STACK_CONS"] = (SExpressions.stack_cons(); ok "")

            | dispatch _ = err "UNKNOWN_CMD"

    fun repl () =
        case TextIO.inputLine TextIO.stdIn of
            NONE => ()
          | SOME line =>
                let val trimmed = String.extract (line, 0, SOME (String.size line - 1)) (* drop \n *)
                    val parts = String.tokens (fn c => c = #" ") trimmed
                in (dispatch parts; repl ()) end
end
