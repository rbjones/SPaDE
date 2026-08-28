signature ENCODING_DECODING =
sig

type bytes = Word8Vector.vector
type NTBS = bytes
type NTBSS = bytes
type sequence_number = int

val encode_bytes : bytes -> NTBS
val decode_bytes : NTBS -> bytes

val decode_slice : NTBSS -> int -> int * bytes

val encode_NTBS_list : NTBS list -> NTBSS
val decode_NTBS_list : NTBSS -> NTBS list

val encode_integer : sequence_number -> NTBS
val decode_integer : NTBS -> sequence_number

end

signature LOW_LEVEL_IO =
sig

include ENCODING_DECODING

exception StaleCacheError of string

type NTBS_info = {
  ntbs: NTBS,
  seqno: sequence_number
}

type repo_handle = {
  info_from_seqno: NTBS_info EfficientDictionary.E_DICT,
  info_from_NTBS: sequence_number EfficientDictionary.E_DICT,
  repo_path: NTBSS,
  file_handle: BinIO.instream option,
  vector_length: int,
  next_sequence_number: sequence_number,
  EOF: bool,
  append_mode: bool
}

val open_new_repository : string -> repo_handle

val open_existing_repository_read : string -> repo_handle

val open_existing_repository_append : string -> repo_handle

val close_repository : repo_handle -> unit

val write_bytes : bytes -> sequence_number

val commit_changes : repo_handle -> unit

val get_sequence_number : bytes -> sequence_number option

val get_bytes : sequence_number -> bytes

end

signature S_EXPRESSIONS =
sig
include LOW_LEVEL_IO

val write_nil : unit -> sequence_number
val write_atom : bytes -> sequence_number
val write_cons : sequence_number * sequence_number -> sequence_number
val write_list : sequence_number list -> sequence_number

val push_nil : unit -> unit
val push_atom : bytes -> unit
val cons_stack : unit -> unit

val push_list : sequence_number list -> unit

datatype sexp =
  Nil
| Atom of bytes
| Cons of sequence_number * sequence_number

val read_sexp : sequence_number -> sexp
val write_sexp : sexp -> sequence_number

val pop_sexp : unit -> sexp
val push_sexp : sexp -> unit

datatype vexp =
  NilValue
| AtomValue of bytes
| ConsValue of vexp * vexp

val write_recursive : vexp -> sequence_number
val read_recursive : sequence_number -> vexp

val push_recursive : vexp -> unit
val pop_recursive : unit -> vexp
end;

"S-EXPRESSIONS";

signature SPADE_ENVIRONMENT =
sig
include S_EXPRESSIONS

type sname = bytes
type rpath = int * sname list
type bpath = NTBSS

val rpath2bpath : rpath -> bpath
val bpath2rpath : bpath -> rpath

val tcsig : int EfficientDictionary.E_DICT
val csig : vexp EfficientDictionary.E_DICT
end;

"SPADE_SIGNATURE";

signature SPADE_ENVIRONMENT =
sig
include S_EXPRESSIONS
end

signature SPADE_REPOSITORY =
sig
include SPADE_ENVIRONMENT

val write_sconstructor : int * sequence_number list -> sequence_number
val read_sconstructor : sequence_number -> (int * sequence_number list)

val push_sconstructor : int * sequence_number list -> unit
val pop_sconstructor : unit -> (int * sequence_number list)

end

