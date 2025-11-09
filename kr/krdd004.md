# Detail description of Procedures for SPaDE Native Repository I/O

This document describes the procedures for reading and writing [SPaDE](../docs/tlad001.md#spade) native repositories in sufficent detail to guide implementation.

In first drafts of this document the procedures defined are those necessary to write a [SPaDE](../docs/tlad001.md#spade) respository from scratch, and to read an existing repository into a suitably structured representation.

Some of the detail will depend upon the language in which the procedures are implemented.
Where possible pertinent differences will be highlighted.
Only two languages are currently under consideration, SML (for HOL4 and ProofPower HOL implementations) and Python (for MCP server implementations).
The Python implementation is now intended to come first.
The former are only intended for the export of theory heirarchies from existing HOL ITP systems into [SPaDE](../docs/tlad001.md#spade) repositories, while the latter are intended for use in delivering the broader functionality of [SPaDE](../docs/tlad001.md#spade) through the logical kernel, deductive intelligence and MCP server subsystems.
Python may also to be used in due course for export of theories from Lean.

For the earliest prototyping the requirement is for SML procedures to write [SPaDE](../docs/tlad001.md#spade) repositories from scratch, and Python procedures to read such repositories into suitable structured representations.

- [Context](#context)
- [Modules](#modules)

## Context

The following documents provide context for understanding the procedures described here:
The [SPaDE](../docs/tlad001.md#spade) native repository format is described in [krdd002.md](krdd002.md).

## Modules

Exactly what these are depends on the language.
In SML they will be SML modules, viz signatures, structures, or functors, while in Python they will be abstract base classes and then the class implementation.

- [Encoding/Decoding](#encodingdecoding)
- [Low Level I/O](#low-level-io)
- [S-Expressions](#s-expressions)

### Encoding/Decoding

The SPaDE native repository is a sequence of null terminated byte sequences.
It is necessary to have procedures for encoding arbitrary byte sequences as null terminated byte sequences, and for decoding such sequences back into arbitrary byte sequences.

This module provides procedures for encoding and decoding null terminated byte sequences into a small number of primitive data types, as follows:
    - byte sequences
    - strings
    - positive integers (natural numbers)
    - sequences (lists) of null terminated byte sequences

When encoding integers, the integer is first represented as a sequence of bytes in big-endian order base 256, and then that byte sequence is encoded as a null terminated byte sequence using the procedure for encoding byte sequences.
Decoding first decodes a null terminated byte sequence into a byte sequence, and then interprets that byte sequence as a big-endian representation of an integer.

The final provision allows that a single null terminated byte sequence can be used to represent a list of such sequences.
This is achieved by appending the null terminated byte strings and then encoding that as a single null terminated byte sequence, using the previously described procedure for encoding byte sequences.
The null terminatory of the individual byte sequences will then be escaped during encoding and restored when decoding.

The coding of byte sequnces into null terminated form is as follows:

The following escape convention will be used to permit the inclusion of null bytes in null terminated byte sequences.
Binary 1 will be used as an escape character to permit a zero byte to be included.
It also serves to escape itself, so that any occurrence of the byte 1 in a byte sequence is represented in a null terminated byte sequence by the two byte sequence 1 1.
When preceding a byte 0, binary 1 indicates that the 0 is to be included in the byte sequence rather than terminating it.
When preceding a byte other than 0 or 1, binary 1 does not function as an escape, and is simply part of the byte sequence.

Decoding a null terminated byte sequence into a byte sequence therefore involves reading bytes until a byte 0 is reached, and interpreting any byte 1 as an escape character.
If the byte following a byte 1 is a byte 0, then a byte 0 is included in the byte sequence.
If the byte following a byte 1 is another byte 1, then a byte 1 is included in the byte sequence.
If the byte following a byte 1 is any other byte, then both the byte 1 and the following byte are included in the byte sequence.
All other bytes are included in the byte sequence until an unescaped byte 0 is reached

### Low Level I/O

This module provides low level procedures for reading and writing [SPaDE](../docs/tlad001.md#spade) native repositories as sequences of null terminated byte sequences held in linear binary files.
It also operates a byte sequence cache, which is an array of byte sequences in the order in which they occur in the file, complemented by and efficient means of retrieving the sequence number of a byte sequence already in the cache.

When reading a repository, the entire file is read and the byte sequences are stored in the cache and associated with their sequence numbers (indices into the array).
When writing a repository, byte sequences are first sought in the cache of sequences already in the file.
If the sequence is found in the cache, it is not written to the file and its sequence number is returned.
If the sequence is not found in the cache, it is allocated the next sequence number, written to the file and also stored in the cache.
When appending to an existing repository, byte sequences are written to the end of the file (if not already present)and also stored in the cache.
Links within the repository are represented as sequence numbers, which are indices into this array.

It is necessary to be able to operate simultaneously on more than one repository file, so the procedures in this module will operate on a repository handle, which encapsulates the file handle and the byte sequence cache for that file.

The operations required are:

1. [Open new repository for writing](#open-new-repository-for-writing)
2. [Open existing repository for reading](#open-existing-repository-for-reading)
3. [Open existing repository for appending](#open-existing-repository-for-appending)
4. [Close repository](#close-repository)
5. [Read byte sequence from repository](#read-byte-sequence-from-repository)
6. [Write byte sequence to repository](#write-byte-sequence-to-repository)
7. Retrieve byte sequence from cache by sequence number
8. Retrieve sequence number from cache by byte sequence

#### Open new repository for writing

The file should be opened in append mode, so that new byte sequences written to the repositoryare added to the end of the file (which will be empty when creating a new repository).

A new empty byte sequence cache should be created.

In order to provide for variations in the SPaDE native repository format which may arise in future, the open new repository procedure will take as arguments a version number.
When creating a new respository, the version number will be written as the first byte sequence in the file.
The current version number is 1 and is written as a null terminated byte sequence representing the integer 1.

This will also be the first entry in the byte sequence cache, and will be elegible for use whenever the version number is required in the repository for whatever purpose.

#### Open existing repository for reading

The cache should cleared first if it is not already empty.
The file should then be opened for reading, and the entire repository read and cached using the procedure described below.
It should then be closed again.

#### Open existing repository for appending

The file must first be opened for reading to read and cache the entire repository, unless it has already been opened for reading and the cache has not been cleared since then.
The file should then be closed and opened in append mode, so that new byte sequences written to the repository are added to the end of the file.

#### Close repository

This would only be called after writing or appending to a repository, or in the prelude to opening an existing repository for appending.
The file should be closed.
The cache should remain available for further use, as is required after reading an existing repository preparatory to appending new byte sequences to it.

#### Read byte sequence from repository

This procedure reads the next null terminated byte sequence from the repository file, decodes it into a byte sequence, adds it to the cache, and returns both the byte sequence and its sequence number (index into the cache).

#### Write byte sequence to repository

This procedure takes as argument a byte sequence to be written to the repository file.
It first checks whether the byte sequence is already present in the cache.
If it is present, its sequence number (index into the cache) is returned without writing anything to the file.
If it is not present, it is added to the cache at the next available index, written to the end of the file in null terminated form, and its sequence number is returned.

#### Retrieve sequence number from cache by byte sequence

This procedure takes as argument a byte sequence and returns its sequence number (index into the cache) if it is present in the cache, and an indication that it is not present if that is the case.
It is for use prior to writing a byte sequence to the repository, to determine whether it is already present and need not therefore be written again.

The values of these two forms are to be returned after each read or write operation.

In order to support these functions, open append will only be allowed when a file has already been opened for reading, and is positioned at the end of the file, so that file position and sequence count are properly maintained.

### S-Expressions

A module will be provided for reading and writing S-expressions using the low level I/O and encoding/decoding modules.
These S-Expressions are represented using null terminated byte sequences as follows:

Each S-expression is either Nil, an atoms (a null terminated byte sequence) or a CONS cell (pairs of pointers to S-expressions).
Each such S-expression will be represented in the linear file as a single null terminated by sequence, which when decoded by elimination of escapes would yield a sequence of one two or three null terminated byte sequences, of which the first indicates the type of S-expression represented, and the remainder give the content of the S-expression.
The first byte sequence is a single byte, with value 0, 1 or 2, which indicates whether the S-expression is Nil, an atom, or a CONS cell respectively, and also inducates how many further byte sequences follow it in the representation of the S-expression.

After decoding first sequence would be a single byte giving the type of S-expression it represents.
If the first byte is 0, the S-expression is Nil, and there are no further byte sequences in the representation.
If the first byte is 1, the S-expression is an atom, and the remainder of the byte sequence represents the atom itself.
If that byte is 2, the S-expression is a CONS cell, and the two subsequent null terminated byte sequences are the sequence numbers of the two S-expressions which are the CAR and CDR of the CONS cell.

Pointers to S-expressions are represented by the sequence number of the null terminated byte sequence representing the expression in the repository.
The module will provide procedures for reading and writing S-expressions to and from the repository file, using the low level I/O and encoding/decoding modules.

The procedures required are:

1. [Write Nil S-expression](#write-nil-s-expression)
2. [Write atom S-expression](#write-atom-s-expression)
3. [Write CONS cell S-expression](#write-cons-cell-s-expression)
4. [Read S-expression](#read-s-expression)

#### Write Nil S-expression

This procedure writes a Nil S-expression to the repository file.
It creates a null terminated byte sequence representing the S-expression and writes it to the file.

#### Write atom S-expression

This procedure writes an atom S-expression to the repository file.
It takes a byte sequence which is the value of the atom, creates a null terminated byte sequence representing it as an S-expression and writes it to the file (unless already in the cache) returning its sequence number.

#### Write CONS cell S-expression

This procedure writes a CONS cell S-expression to the repository file.
It takes two byte sequences numbers which are the CAR and CDR of the CONS cell and must already be in the cache, and creates a null terminated byte sequence representing the S-expression and if new writes it to the file, otherwise retrieves its sequence number from the cache.

#### Read S-expression

This procedure extracts a S-expression from the cache.
It decodes a byte sequence in the cache given its sequence number into an S-expression and returns it.
The S-expression is represented as either:

- Nil
- An atom byte sequence
- A pair of sequence numbers representing the CAR and CDR of a CONS cell
