structure EncodingDecoding : ENCODING_DECODING =
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
                                [] => raise Fail "Unexpected EOF after escape"
                            | 0w0 :: tl => step (tl, 0w0 :: acc)
                            | 0w1 :: tl => step (tl, 0w1 :: acc)
                            | b :: tl => step (tl, b :: 0w1 :: acc))
                    | step (0w0 :: tl, acc) = rev acc
                    | step (b :: tl, acc) = step (tl, b :: acc)
            in
                Word8Vector.fromList (step (Word8Vector.foldr op:: [] data, []))
            end

    fun encode_integer n =
            if n < 0 then raise Fail "encode_integer: negative"
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
                    | split (0w1 :: 0w0 :: tl, current, acc) = split (tl, 0w0 :: current, acc)
                    | split (0w1 :: 0w1 :: tl, current, acc) = split (tl, 0w1 :: current, acc)
                    | split (0w1 :: b :: tl, current, acc) = split (tl, b :: 0w1 :: current, acc)
                    | split (b :: tl, current, acc) = split (tl, b :: current, acc)
            in
                split (Word8Vector.foldr op:: [] data, [], [])
            end
end


structure LowLevelIO : LOW_LEVEL_IO =
struct
    type byte_sequence = EncodingDecoding.byte_sequence
    type sequence_number = int

    exception StaleCacheError of string

    val filepath : string option ref = ref NONE
    val cache : byte_sequence list ref = ref []
    val cache_map : (byte_sequence * sequence_number) list ref = ref []
    val file_size : int ref = ref 0

    fun reset () = (filepath := NONE; cache := []; cache_map := []; file_size := 0)

    fun find_seq data =
            let
                fun loop [] = NONE
                    | loop ((d,n)::tl) = if Word8Vector.equals (d,data) then SOME n else loop tl
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
                cache_map := ListPair.zip (seqs, List.tabulate (length seqs, fn i => i));
                file_size := Word8Vector.length data
            end

    fun open_existing_repository_append path =
            (case (!filepath, !cache) of
                    (SOME _, _) =>
                        let val size_on_disk = OS.FileSys.fileSize path
                        in if size_on_disk <> LargeInt.fromInt (!file_size) then
                                raise StaleCacheError "File changed on disk"
                            else () end
                | _ => raise Fail "Must read repository before append")

    fun close_repository () = reset()

    fun read_byte_sequence () =
            raise Fail "read_byte_sequence: use open_existing_repository_read instead"

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
    fun get_byte_sequence n = List.nth (!cache, n)
end


structure SExpressions : S_EXPRESSIONS =
struct
    type byte_sequence = LowLevelIO.byte_sequence
    type sequence_number = LowLevelIO.sequence_number

    datatype sexp = Nil | Atom of byte_sequence | Cons of sequence_number * sequence_number
    datatype sexp_value =
        NilValue
    | AtomValue of byte_sequence
    | ConsValue of sexp_value * sexp_value

    val encoding = EncodingDecoding

    fun write_nil () =
            LowLevelIO.write_byte_sequence (encoding.encode_sequence_list [Word8Vector.fromList [0w2]])

    fun write_atom v =
            LowLevelIO.write_byte_sequence (encoding.encode_sequence_list [Word8Vector.fromList [0w3], v])

    fun write_cons (car_seq, cdr_seq) =
            let
                val car_bytes = encoding.encode_integer car_seq
                val cdr_bytes = encoding.encode_integer cdr_seq
            in
                LowLevelIO.write_byte_sequence (encoding.encode_sequence_list [Word8Vector.fromList [0w4], car_bytes, cdr_bytes])
            end

    fun read_sexpression seq_num =
            let
                val raw = LowLevelIO.get_byte_sequence seq_num
                val parts = encoding.decode_sequence_list raw
            in
                case parts of
                    [] => raise Fail "Empty S-expression payload"
                | tag :: rest =>
                    if tag = Word8Vector.fromList [0w2] then Nil
                    else if tag = Word8Vector.fromList [0w3] then
                            (case rest of
                                    v :: _ => Atom v
                                | _ => raise Fail "Atom missing value")
                        else if tag = Word8Vector.fromList [0w4] then
                                (case rest of
                                        carb :: cdrb :: _ => Cons (encoding.decode_integer carb, encoding.decode_integer cdrb)
                                    | _ => raise Fail "Cons missing pointers")
                            else raise Fail "Unknown S-expression type"
            end

    val stack : sequence_number list ref = ref []

    fun push_nil () = stack := write_nil() :: (!stack)
    fun push_atom v = stack := write_atom v :: (!stack)

    fun stack_cons () =
            (case !stack of
                    cdr :: car :: rest => stack := write_cons (car, cdr) :: rest
                | _ => raise Fail "Stack underflow")

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
