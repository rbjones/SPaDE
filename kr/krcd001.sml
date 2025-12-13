(*
   Signature for SPaDE Native Repository low-level I/O
   Mirrors the Python ABCs in krcd008.py (encoding/decoding, low-level IO,
   and S-expression helpers) so the SML implementation can expose the same
   contract.
*)

signature ENCODING_DECODING =
sig
    type byte_sequence = Word8Vector.vector

    val encode_bytes : byte_sequence -> byte_sequence
    val decode_bytes : byte_sequence -> byte_sequence

    val encode_integer : int -> byte_sequence
    val decode_integer : byte_sequence -> int

    val encode_sequence_list : byte_sequence list -> byte_sequence
    val decode_sequence_list : byte_sequence -> byte_sequence list
end


signature LOW_LEVEL_IO =
sig
    type byte_sequence = ENCODING_DECODING.byte_sequence
    type sequence_number = int

    exception StaleCacheError of string

    val open_new_repository : string * int -> unit
    val open_existing_repository_read : string -> unit
    val open_existing_repository_append : string -> unit
    val close_repository : unit -> unit

    val read_byte_sequence : unit -> byte_sequence * sequence_number
    val write_byte_sequence : byte_sequence -> sequence_number
    val get_sequence_number : byte_sequence -> sequence_number option
    val get_byte_sequence : sequence_number -> byte_sequence
end


signature S_EXPRESSIONS =
sig
    type byte_sequence = LOW_LEVEL_IO.byte_sequence
    type sequence_number = LOW_LEVEL_IO.sequence_number

    datatype sexp = Nil | Atom of byte_sequence | Cons of sequence_number * sequence_number
    datatype sexp_value =
        NilValue
    | AtomValue of byte_sequence
    | ConsValue of sexp_value * sexp_value

    val write_nil : unit -> sequence_number
    val write_atom : byte_sequence -> sequence_number
    val write_cons : sequence_number * sequence_number -> sequence_number

    val read_sexpression : sequence_number -> sexp

    val push_nil : unit -> unit
    val push_atom : byte_sequence -> unit
    val stack_cons : unit -> unit

    val write_recursive : sexp_value -> sequence_number
    val read_recursive : sequence_number -> sexp_value
end

