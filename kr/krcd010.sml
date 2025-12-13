signature ENCODING_DECODING =
sig
    (*
      Encode/decode routines that perform null-terminated byte sequence (NTBS)
      escaping as described in krdd004. Each NTBS carries the terminator that
      defines the encoding in the design document.
    *)
    type byte_sequence = Word8Vector.vector

    val encode_bytes : byte_sequence -> byte_sequence
     (* Encode an arbitrary byte sequence into an escaped NTBS (terminator is
       appended as part of the encoding). *)

    val decode_bytes : byte_sequence -> byte_sequence
     (* Decode an escaped NTBS payload back to the original bytes, interpreting
       the terminator as the end of the payload. *)

    val encode_integer : int -> byte_sequence
     (* Encode a non-negative integer into big-endian bytes and represent the
       result as an NTBS. *)

    val decode_integer : byte_sequence -> int
    (* Decode the big-endian bytes of an NTBS back into an integer. *)

    val encode_sequence_list : byte_sequence list -> byte_sequence
     (* Concatenate multiple NTBS payloads into one stream that can be written
       sequentially. *)

    val decode_sequence_list : byte_sequence -> byte_sequence list
     (* Split a streamed NTBS payload into individual NTBS items, reversing the
       effect of [encode_sequence_list]. *)
end

signature LOW_LEVEL_IO =
sig
    (*
      Minimal repository reader/writer that keeps a cache of byte sequences and
      performs optimistic locking during append operations.
    *)
    type byte_sequence = Word8Vector.vector
    type sequence_number = int

    exception StaleCacheError of string
    (* Raised when the on-disk file no longer matches the cached length. *)

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
  type byte_sequence = Word8Vector.vector
  type sequence_number = int

  datatype sexp =
      Nil
    | Atom of byte_sequence
    | Cons of sequence_number * sequence_number

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