# SPaDE native repository SML interface

This document describes the SML interface to the SPaDE native repository.
It is presented as a set of signatures for the various layers in the interface which are:

- [Encoding and Decoding](#encoding-and-decoding)
- [Low-Level I/O](#low-level-io)
- [S-Expressions and Lists](#s-expressions-and-lists)
- [Higher Structures](#higher-structures)

## Encoding and Decoding

The repository is a sequence of null terminated byte sequences (NTBS).
Because a zero byte terminates the NTBS, an escape convention is required to allow zero bytes to be included in the byte sequences.
We therefore require procedures for creating NTBS which insert escapes as needed and add the terminating zero, and for decoding NTBS which remove the escapes and the terminator to give the original byte sequence.

The NTBS are used to represent S-expressions.
This determines the requirements for encoding and decoding at this level.
It involves packing more than one constituent into a single NTBS, in which case each constituent is given as an NTBS and the whole is then encoded as a single NTBS which we speak of as an NTBSS.
This repeated encoding gives us three different uses of byte sequences, all of which are at bottom WORD8 vectors, but which are used in different ways and therefore have different type names in the SML signatures to make clear the depth of encoding required in parameters and delivered in results.

They are named *bytes*, *NTBS* and *NTBSS*, and the encoding and decoding procedures are defined to convert between these different types as required.

The required conversions are therefore to and from:

- [Byte Sequences](#byte-sequences)
- [Sequences (lists) of NTBS](#sequences-lists-of-ntbs)
- [Integers](#integers)

```sml
signature ENCODING_DECODING =
sig
```

The procedures defined below operate both on arbitrary byte sequences (of known length) and on null terminated byte sequences (NTBS), which are byte sequences terminated by a null byte (byte 0), and on byte vectors which are sequences of NTBS.
The NTBS form allows bytes sequences to be concatenated (to form NTBSS)without loss of information about their length, and is the form used for storage in the repository.
The representation for both of these forms is the same (WORD8Vector.vector), but to make clear which is which, the type of byte sequences is used for the former, and the type of NTBS or NTBSS is used for the latter.
Procedures taking NTBS parameters will work only with the bytes up to and including the first null terminator, will ignore any bytes following the first null terminator.
NTBSS are sometimes unpacked as a whole into a sequence of NTBS, and sometimes unpacked one at a time, yielding the first NTBS and the trailing NTBSS or an index into the NTBSS.

An NTBS is a byte sequence and is therefore represented as a vector of 8-bit words.
Though the types are the same, the distinction between byte sequences and NTBS is important the these two distinct names for the same type are used to make clear which is required or delivered by any of the procedures in the signature.

```sml
type bytes = Word8Vector.vector
type NTBS = bytes
type NTBSS = bytes
type sequence_number = int
```

### Byte Sequences

The algorithm for encoding and decoding byte sequences as NTBS is as follows:

The following escape convention will be used to permit the inclusion of null bytes in null terminated byte sequences.
Binary 1 will be used as an escape character to permit a zero byte to be included.
It also serves to escape itself, so that any occurrence of the byte 1 in a byte sequence is represented in a null terminated byte sequence by the two byte sequence 1 1.
When preceding a byte 0, binary 1 indicates that the 0 is to be included in the byte sequence rather than terminating it.
When preceding a byte other than 0 or 1, binary 1 does not function as an escape, and is simply part of the byte sequence.
When appearing at the end of a byte sequence being encoded, binary 1 must be escaped in the resulting NTBS since it would otherwise escape the null terminator.
Decoding a null terminated byte sequence into a byte sequence therefore involves reading bytes until a byte 0 is reached, and interpreting any byte 1 as an escape character.
If the byte following a byte 1 is a byte 0, then a byte 0 is included in the byte sequence.
If the byte following a byte 1 is another byte 1, then a byte 1 is included in the byte sequence.
If the byte following a byte 1 is any other byte, then both the byte 1 and the following byte are included in the byte sequence.
All other bytes are included in the byte sequence until an unescaped byte 0 is reached.

```sml
val encode_bytes : bytes -> NTBS
val decode_bytes : NTBS -> bytes
```

The following procedure might be used for progressively decoding the sequence of NTBS which form a SPaDE repository.

The integer supplied is the index of the first byte of the NTBS to be decoded in the NTBSS, and the result is a pair of the index of the first byte of the next NTBS in the NTBSS and the decoded NTBS.

```sml
val decode_slice : NTBSS -> int -> int * bytes
```

### Sequences (Lists) of NTBS

To pack a list of NTBS into a single NTBS, first concatenate the elements of the list into a single byte sequence, and then encode that byte sequence as an NTBS.
To decode, first decode the NTBS into a byte sequence, and then split that byte sequence into the original list of NTBS by splitting on the terminator byte, ignoring escaped terminators.

```sml
val encode_NTBS_list : NTBS list -> NTBSS
val decode_NTBS_list : NTBSS -> NTBS list
```

### Integers

When encoding integers, the integer is first represented as a sequence of bytes in big-endian order base 256, and then that byte sequence is encoded as a null terminated byte sequence using the procedure for encoding byte sequences.
Decoding first decodes a null terminated byte sequence into a byte sequence, and then interprets that byte sequence as a big-endian representation of an integer.
These integers are primarily used in the SPaDE repository as sequence numbers in CONS cells, which are used to refer to byte sequences in the repository, but may also be used for atoms.

```sml
val encode_integer : sequence_number -> NTBS
val decode_integer : NTBS -> sequence_number

end
```

## Low-Level I/O

```sml
signature LOW_LEVEL_IO =
sig

include ENCODING_DECODING
```

Low-level I/O is concerned with reading and writing byte sequences to and from the repository file, with maintaining a cache of byte sequences read from the repository file, and performing optimistic locking when committing append operations to the repository file.

When updating a repository, the repository must first be read to construct the cache.
Amendments to the repository are first made to the cache, only appended to the repository file when the changes are committed.

 If a repository is first opened for reading, and then for writing, it is necessary to check that the repository has not been updated in the meantime, and if it has, a StaleCacheError should be raised, since the cache is now stale and cannot be used to write to the repository.

The following exception is to be raised when the on-disk file no longer matches the cached length, which will be checked when opening a repository for appending, after it was previously open for reading.

```sml
exception StaleCacheError of string
```

The required operations are as follows:

- [Open a new repository](#open-a-new-repository)
- [Open an existing repository for reading](#open-an-existing-repository-for-reading)
- [Open an existing repository for appending](#open-an-existing-repository-for-appending)
- [Close a repository](#close-a-repository)
- [Read a byte sequence](#read-a-byte-sequence)
- [Write a byte sequence](#write-a-byte-sequence)
- [Get the sequence number for a byte sequence](#get-the-sequence-number-for-a-byte-sequence)
- [Get the byte sequence for a sequence number](#get-the-byte-sequence-for-a-sequence-number)

### Open a new repository

Each repository is associated with caches and other data structures which are used to manage access to the repository.
These are initialised when a new repository is opened and are made available for operations on the repository via the repository handle returned by the open operation.
The repository handle incorporates the handle of the underlying linear file.

Efficient dictionaries are required for the implementation of the cache, for which the ProofPower EfficientDictionary is available for use of a repository manager in that context, and may be imported into other contexts using SML.
Similar facilities will also be required in python and possibly other languages for SPaDE repository functionality in other contexts.

This information includes:

- for each NTBS in the repository:
  - the byte sequence of the NTBS (including the terminator)
  - the sequence number of the NTBS (which is unique for each NTBS in the repository)
- The necessary indexes to allow efficient retrieval of the byte sequence  for a given sequence number, and of the sequence number for a given byte sequence.
- the physical position of the end of the file
- the sequence number of the last byte sequence in the repository
- the current sequence number (starts at 1, for the first NTBS after the version number, and is the sequence number of the next byte sequence to be written to or read from the repository)
- EOF - a flag indicating either that the repository has been completely read and the current sequence number is not in the file, or that it is in append mode and the current sequence number is that of the next NTBS to be written to the repository
- a flag indicating whether the repository is open for reading or appending
- the file handle for the repository file

The following facilities should be supported for concurrent access to multiple repositories.
Since access to these repositories involves the construction of caches which support navigation in the repository and avoid duplication of data, each open repository must have its own cache, and the operations on the repository must be performed in the context of that cache.

Though the facilities might appear to incrementally read from or write to the repository file, in practice the whole file will be read into memory when a repository is opened, and updates to the repository (which will be made by appending to the file since it is a WORM repo) will be cached in memory and written to the file only when the edits are committed.

All the data specific to a SPaDE native repository is encapsulated in the repository handle, which is returned by the open operations and passed to all subsequent operations on the repository.
Further detail on the content of the repository handle is given in the description of the [open-a-new-repository](#open-a-new-repository) operation below.

In the following repo-handle type, the information associated with each NTBS in the repository includes derived data, notably the sexpr and vexpr derived from the NTBS if that computation has been performed, and the sequence number of the NTBS, which is unique for each NTBS in the repository.

```sml
type NTBS_info = {
  ntbs: NTBS,
  sexpr: ref sexp,
  vexpr: ref vexp,
  seqno: sequence_number
}
```

Access to the NTBS from the sequence number is mediated in two distinct ways.
The NTBS already in a repository when it is opened may be accessed using a vector, which is indexed by the sequence number of the NTBS, and which gives the NTBS_info for that NTBS.
This vector is initialised when the repository is opened, by reading the entire repository file and decoding the NTBS into the cache.
When additional information is written to the repository, it is stored in an efficient dictionary, which is indexed by the sequence number of the NTBS, and which gives the NTBS_info for that NTBS.
When it is required to access an NTBS by its sequence number, the vector is checked first, and if the sequence number is not in the vector, then the efficient dictionary is checked.
The sexp and vexp fields are initially Nil references, and are updated when the sexp or vexp for that NTBS is computed, so that subsequent access to the sexp or vexp for that NTBS can be obtained from the cache without recomputation.
When writing to a repository, these will often already be available, depending on the interface used for the write, the higher level for used writing a vexp will first of all write the constituents of the vexp to the repository, and then write the top level of the vexp as an NTBS (possibly presented as a Sexp), creating the new cache entry on completion of the write.

```sml
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
```

The first NTBS in a repository identifies the version of the repository format, and is written when the repository is created and read when the repository is opened for reading or appending. This indicates the format of the repository, and therefore how to read and write byte sequences to and from the repository.
This will usually be hard coded into the software managing the repo, and for the initial version of the repository format (which is described here) will be 1.

```sml
val open_new_repository : string -> repo_handle
```

### Open an existing repository for reading

When an existing repository, the required data is set up in the first instance as in creating a new repository, except that instead of writing a version number NTBS to the file, the first NTBS is checked to ensure it is supported by the current version of the software (which in this case is 1).
The entire repository is then read and its data cached, including the location and sequence number of the last NTBS, which is the head of the most recent commit to the repository.

```sml
val open_existing_repository_read : string -> repo_handle
```

### Open an existing repository for appending

When an existing repository is opened for appending, the same initialisation is performed as when opening for reading, but with the additional requirement that the repository has not been updated since it was last read, which is checked by comparing the sequence number of the last NTBS in the repository with the sequence number of the last NTBS in the cache. If they do not match, a StaleCacheError is raised.

```sml
val open_existing_repository_append : string -> repo_handle
```

### Close a repository

When a repository is closed, any updates to the repository must be written to the file, and the cache must be cleared.

```sml
val close_repository : repo_handle -> unit
```

### Read a byte sequence

Given a sequence number, return the byte sequence of the corresponding NTBS in the repository.

```sml
val read_bytes : repo_handle -> (bytes * sequence_number) option
```

### Write a byte sequence

Given a byte sequence, write it to the end of the repository file as an NTBS and return its sequence number.

```sml
val write_bytes : bytes -> sequence_number
```

### Get the sequence number for a byte sequence

Given a byte sequence, return its sequence number if it is in the repository, or NONE if it is not.

```sml
val get_sequence_number : bytes -> sequence_number option
```

### Get the byte sequence for a sequence number

Given a sequence number, return its byte sequence if it is in the repository, or raise an exception if it is not.

```sml
val get_bytes : sequence_number -> bytes

end
```

## S-Expressions and Lists

```sml
signature S_EXPRESSIONS =
sig
include LOW_LEVEL_IO
```

The NTBS in the SPaDE native repository are exclusively used to represent "s-expressions", which are either: Nil, an Atom (a byte sequence), or a Cons cell (a pair of sequence numbers which refer to other s-expressions in the repository).
The NTBS represents the s-expression by using a sequence of NTBS the first of which is gives the type of the s-expression, which will be either 2, 3 or 4.

The remaining NTBS constituents are as follows:

- For a Nil s-expression, there are no remaining NTBS.
- For an Atom s-expression, there is one remaining NTBS which gives the byte sequence of the atom.
- For a Cons cell s-expression, there are two remaining NTBS which give the sequence numbers of the two s-expressions which are the Car and Cdr of the Cons cell.

The following operations check whether an NTBS representing an s-expression is in the repository and if so return its sequence number, otherwise they write the NTBS to the repository and return the new sequence number.
Note that the byte sequences passed to and from these procedures are not the that of the s-expression, but those of its constituents (if any), and they are plain byte sequences, not NTBS, but need to be converted from or to NTBS when extracted from or placed in the NTBS for the s-expression.

```sml
val write_nil : unit -> sequence_number
val write_atom : bytes -> sequence_number
val write_cons : sequence_number * sequence_number -> sequence_number
val write_list : sequence_number list -> sequence_number
```

The following operations provide for the use of a stack while writing s-expressions.
At this point it is unclear whether this is necessary, but it may be useful for writing higher structures such as lists and trees of s-expressions.

```sml
val push_nil : unit -> unit
val push_atom : bytes -> unit
val cons_stack : unit -> unit
```

The s-expressions are primarily used at higher levels for the construction of lists, so it is convenient to have operations for prepending a list of s-expressions (as sequence numbers) to the list pointed to from by the top of the stack.

consing lists of s-expressions onto the s-expression pointed to by the top of the stack, leaving the new list (the appending of the top of stack to the list supplied) on the top of the stack.

```sml
val push_list : sequence_number list -> unit
```

In addition to the representation of s-expressions as NTBS, it is also useful to have representations of s-expressions as SML datatypes.

There are two levels of representation as SML datatypes, one which is non-recursive and corresponds directly to the NTBS representation, and one which is recursive and corresponds more closely to the usual notion of s-expressions as either Nil, an atom or a cons cell of s-expressions.

Operations on the non-recursive representation are as follows:

```sml
datatype sexp =
  Nil
| Atom of bytes
| Cons of sequence_number * sequence_number

val read_sexp : sequence_number -> sexp
val write_sexp : sexp -> sequence_number

val pop_sexp : unit -> sexp
val push_sexp : sexp -> unit
```

Operations on the recursive representation are as follows:

```sml
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
```

## Higher Structures

Higher structures are uniformly represented as s-expression lists, which is to say, s-expressions obtained by repeatedly adding a new head (using Cons) to the empty list represented by Nil.
The elements of such a list may be any s-expression (but are also likely to be either atoms or lists), but they are constrained by the grammar and typing rules of HOL types and terms and the required structure of the repository.
The first element of each such list is an atom indicating the type of construction represented by the list, which will determine the length of the list (following the abstract syntax), and the abstract syntax then also determines what kinds of construction are permitted for each of the subsequent elements of the list.

Further well-formedness constraints depend on the available vocabulary and on constraints on the arity of type constructors and the types of constants previously introduced.
The availability of vocabulary is constrained by the theory hierarchy.
Only names defined in the current theory or its ancestors are available for use in the current theory, and the arity of type constructors and the types of constants are subject to the constraints imposed when they were introduced.

The current *context* is determined by the most recent extension undertaken in the repository, even if that has not yet been committed to the repository file.
Each such context has an associated *environment* in which is recorded the signatures of all names in scope, which are those in ancestors of the current theory, and those previously introduced to the current theory, together with the constraints imposed on those constants when they were introduced, and all theorems stored so far in the current theory and its ancestors.

Because of the relative nature of constant references, it is desirable to normalise to the current context the names of all instances of type constructors and constants to the current context.
Normalisation of names depends only on the current theory, not to position in that theory,
and therefore takes place on opening a theory, and involved adjusting the environment created by each parent theory and merging them together.
It is possible to retrict the names exported from a theory, and thereby to restrict the theorems exported from the theory.

Because of the environmental sensitivity of the well-formedness constraints, the higher level structures of the SPaDE repository are presented in an order which permits the environment to be defined before any structure whose well-formedness depends upon it.
The environment is not a structure which is stored in the repository, but is a convenient condensation of the relevant parts of that information in any particular context.

### Contexts and Environments

A SPaDE repository determines two hierarchies.
The first is a namespace hierarchy in which every type constructor or constant is given a unique identity in a manner similar to paths in a filestore or URLs.
The second is a hierarchy of *contexts*.
Contexts determine subspaces of the global namespace which are accessible at any location in the repository.
The context hierarchy has a coarse structure determined by the parent-child relationships between theories, and a finer structure determined by the order in which extensions are undertaken in the each theory.
A context is identified either by the path to a theory, or by the path to a particular extension in a theory.

Each context has an associated *environment* which records the available vocabulary and the constraints on that vocabulary, which are used to determine the well-formedness of HOL types and terms, and of the repository structures which represent them.
If the context is a theory, then the environment includes the vocabulary and constraints of all ancestors of that theory in the theory hierarchy, and all of the names introduced in the theory.
If the context is an extension, then the environment includes the vocabulary and constraints of all ancestors of the theory in which the extension is undertaken, together with those of all previous extensions in that theory.

Environments serve two principal purposes.
The first is to determine the well-formedness of HOL types and terms, and of the repository structures which represent them, by recording the available vocabulary and the constraints on that vocabulary.
The second is to normalise relative names in the repository (which are relative to the point of use) to the current context, so that checking the identity of type constructors and constants can be done by checking the identity of their normalised names, which will be identical throughout any single context.

For the purposes of determining well-formedness, the environment needs to record a signature of the available vocabulary, which includes the names of type constructors and constants, the arity of the type constructors, the types of the constants.
The environment also supports reasoning in the language defined by the constraints placed on those contexts, by including for each name in the signature, the defining constraint on its value.
The environment also includes the theorems which have been proved and saved in theories of the current context, and may be used in the derivation of additional theorems.

```sml
signature SPADE_ENVIRONMENT =
sig
include S_EXPRESSIONS
```

The primary purpose of an environment is to document the available vocabulary and the constraints on that vocabulary, which are used to determine the well-formedness of HOL types and terms, and of the repository structures which represent them.

Environments should be implemented using efficient dictionaries, for which an implementation is available in ProofPower (signature in $PPDIR/src/hol/dtd001.pp and implementation in $PPDIR/src/hol/imp001.pp).
Those dictionaries are implemented for string keys, so the following signature includes access functions which accept byte sequences as keys.

For implementation in Python or in environments other than ProofPower, a similar dictionary implementation will be required.

### Names and Paths

Names for type constructors and constants in SPaDE are uniquely identified by their point of introduction, which is referred to by a relative path.
This consists of the identification of the nearest common ancestor in the namespace (not the theory hierarchy) of the defining theory and the using theory, and then the name of the path from there to the point at which the type constructor or constant is introduced.
In the environment associated with a context in a SPaDE repository, the names of type constructors and constants defined in ancestors of the theory are normalised to the current context, so that the relative name of a type constructor or constant is the same wherever it is used in that environment, and checking identity is an equality comparison of NTBSS (*bpath*s).

```sml
type sname = bytes
type rpath = int * sname list
type bpath = NTBSS
```

```sml
val rpath2bpath : rpath -> bpath
val bpath2rpath : bpath -> rpath

val tcsig : int EfficientDictionary.E_DICT
val csig : vexp EfficientDictionary.E_DICT
end;

"SPADE_SIGNATURE";
```

### Environments

```sml
signature SPADE_ENVIRONMENT =
sig
include S_EXPRESSIONS
end
```

### HOL Term Structures

```sml
signature SPADE_REPOSITORY =
sig
include SPADE_ENVIRONMENT
```

Given an account of the abstract syntax which enumerates the available constructors, all this higher level structure can be encoded or decoded using the above constructors, but it may be convenient to interface with the repository at this level with the following procedures.

The presentation falls into the following parts:

- [generic stack based list operations](#generic-stack-based-list-operations)

2 [Constant Names](#constant-names)
3 [HOL Types](#hol-types)
4 [HOL Terms](#hol-terms)
5 [HOL Sequents and Theorems](#hol-sequents-and-theorems)
6 [HOL Signatures](#hol-signatures)
7 [HOL Theories](#hol-theories)
8 [SPaDE Folders](#spade-folders)
9 [SPaDE Commits](#spade-commits)

### Generic Stack Based List Operations

```sml
val write_sconstructor : int * sequence_number list -> sequence_number
val read_sconstructor : sequence_number -> (int * sequence_number list)

val push_sconstructor : int * sequence_number list -> unit
val pop_sconstructor : unit -> (int * sequence_number list)
```

```sml
end
```

### Constant Names

### HOL Types

### HOL Terms

### HOL Sequents and Theorems

### HOL Signatures

### HOL Theories

### SPaDE Folders

### SPaDE Commits
