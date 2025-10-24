# Detail description of Procedures for SPaDE Native Repository I/O

This document describes the procedures for reading and writing [SPaDE](../docs/tlad001.md#spade) native repositories in sufficent detail to guide implementation.

In first drafts of this document the procedures defined are those necessary to write a [SPaDE](../docs/tlad001.md#spade) respository from scratch, and to read an existing repository into a suitably structured representation.

Some of the detail will depend upon the language in which the procedures are implemented.
Where possible pertinent differences will be highlighted.
Only two languages are currently under consideration, SML (for HOL4 and ProofPower HOL implementations) and Python (for MCP server implementations).
The former are only intended for the export of theory heirarchies from existing HOL ITP systems into [SPaDE](../docs/tlad001.md#spade) repositories, while the latter are intended for use in delivering the broader functionality of [SPaDE](../docs/tlad001.md#spade) through the logical kernel, deductive intelligence and MCP server subsystems.
Python may also to be used in due course for export of theories from Lean.

For the earliest prototyping the requirement is for SML procedures to write [SPaDE](../docs/tlad001.md#spade) repositories from scratch, and Python procedures to read such repositories into suitable structured representations.

## Context

The following documents provide important context for understanding the procedures described here:
The [SPaDE](../docs/tlad001.md#spade) native repository format is described in [krdd002.md](krdd002.md).

## Modules

### Low Level I/O Module

This module provides low level procedures for reading and writing [SPaDE](../docs/tlad001.md#spade) native repositories as sequences of null terminated byte sequences held in linear binary files.

The operations required are:

1. Open new file for writing
2. Open existing file for reading
3. Open existing file for appending
4. Close file
5. Write null terminated byte sequence to file
6. Read null terminated byte sequence from file

While underaking these functions the module must maintain the current position in the file in two forms:

1. The byte displacement within the file of the next read or write.  We'll call this the file position, and when preserved in association with the sequence, the sequence position.
2. The count of byte sequences read or written.  We'll call this the sequence count, and when preserved in association with the file position, the sequence number.

The values of these two forms are to be returned after each read or write operation.

In order to support these functions, open append will only be allowed when a file has already been opened for reading, and is positioned at the end of the file, so that file position and sequence count are properly maintained.

### Encoding/Decoding Module

This module provides procedures for encoding and decoding null terminated byte sequences into a small number of primitive data types, as follows:
    - byte sequences
    - strings
    - positive integers (natural numbers)
    - sequences (lists) of null terminated byte sequences

When encoding integers, the integer is first represented as a sequence of bytes in big-endian order base 256, and then that byte sequence is encoded as a null terminated byte sequence using the procedure for byte sequences.
Decoding first decodes a null terminated byte sequence into a byte sequence, and then interprets that byte sequence as a big-endian representation of an integer.

The latter provision allows that a single null terminated byte sequence can be used to represent a list of such sequences.
This is achieved by appending the null terminated byte strings and then encoding that as a single null terminated byte sequence, using exactly the same algorithm as for any other data type.
The null terminatory of the individual byte sequences will then be escaped during encoding and restored when decoding.

The coding of byte sequnces into null terminated form is as follows:

A [SPaDE](../docs/tlad001.md#spade) native repository is a sequence of null terminated byte sequences.
It is necessary to have procedures for encoding arbitrary byte sequences as null terminated byte sequences, and for decoding such sequences back into arbitrary byte sequences.
In doing so the following escape convention will be used.
The binary character 1 will be used as an escape character to permit a zero byte to be included in a byte sequence.
It therefore also serves to escape itself, so that any occurrence of the byte 1 in a byte sequence is represented by the two byte sequence 1 1.
When preceding an byte other than 0 or 1,binary 1 does not function as an escape, and is simply part of the byte sequence.

### S-Expressions

A module will be provided for reading and writing S-expressions using the low level I/O and encoding/decoding modules.
These S-Expressions are represented using null terminated byte sequences as follows:

Each S-expression is either Nil, an atoms (a null terminated byte sequence) or a CONS cell (pairs of pointers to S-expressions).
Each such S-expression will be represented in the linear file as a single null terminated by sequence, which when decoded by elimination of escapes would yield a sequence of null terminated byte sequences.
The first sequence would be a single byte giving the type of S-expression it represents.
If that byte is 0, the S-expression is a CONS cell, and the two subsequent null terminated byte sequences represent the two S-expressions which are the CAR and CDR of the CONS cell.
If the first byte is 1, the S-expression is an atom, and the remainder of the byte sequence represents the atom itself.
If the first byte is 2, the S-expression is Nil, and there are no further byte sequences in the representation.

Pointers to S-expressions are represented by the bsequence number of the null terminated byte sequence representing the expresion in the repository.
