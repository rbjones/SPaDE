# Detail description of Procedures for SPaDE Native Repository I/O

*(version 0.2 in progress:
The central thrust of this change is to change the second layer from an S-expression-like structure, to one closely aligned with JSON since that is the language with which the SPaDE MCP server will engage with its AGI clients.

TO DO: complete the details of this change.
)*

This document describes the procedures for reading and writing [SPaDE](../docs/tlad001.md#spade) native repositories in sufficent detail to guide implementation.

In first drafts of this document the procedures defined are those necessary to write a [SPaDE](../docs/tlad001.md#spade) respository from scratch, and to read an existing repository into a suitably structured representation.

Some of the detail will depend upon the language in which the procedures are implemented.
Where possible, pertinent differences will be highlighted.
Only two languages are currently under consideration, SML (for HOL4 and ProofPower HOL implementations) and Python (for MCP server implementations).
The former are only intended for the export of theory heirarchies from existing HOL ITP systems into [SPaDE](../docs/tlad001.md#spade) repositories, while the latter are intended for use in delivering the broader functionality of [SPaDE](../docs/tlad001.md#spade) through the logical kernel, deductive intelligence and MCP server subsystems.
Python may also to be used in due course for export of theories from Lean.

It is possible that access to non-SPaDE repositories will not be undertaken by writing from their custodians to a SPaDE repository, but via a much simpler export directly to SPaDE facilities implemented in Python.
Either way the Python implementation is  expected to come first.

For the earliest prototyping the requirement is for SML procedures to write [SPaDE](../docs/tlad001.md#spade) repositories from scratch, and Python procedures to read such repositories into suitable structured representations.

The following documents provide context for understanding the procedures described here:
The [SPaDE](../docs/tlad001.md#spade) native repository format is described in [krdd002.md](krdd002.md).

The following sections describe the modules to be implemented, and the procedures within those modules.
The facilities will need to be provided in more than one language, to enable export from various sources of declarative knowledge into SPaDE repositories.

This affects how the requirements are typically described.
In SML they will be SML modules, viz signatures, structures, or functors, while in Python they will be abstract base classes and then the class implementation.

THe modules required are as follows:

- [Encoding/Decoding](#encodingdecoding)
- [Low Level I/O](#low-level-io)
- [J-Expressions](#j-expressions)
- [HOL Terms](#hol-terms)
- [Theories and Folders](#theories-and-folders)

## Encoding/Decoding

The SPaDE native repository is a sequence of null terminated byte sequences (NTBS).
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
When appearing at the end of a byte sequence being encoded, binary 1 must be escaped in the resulting NTSB since it would otherwise escape the null terminator.
Decoding a null terminated byte sequence into a byte sequence therefore involves reading bytes until a byte 0 is reached, and interpreting any byte 1 as an escape character.
If the byte following a byte 1 is a byte 0, then a byte 0 is included in the byte sequence.
If the byte following a byte 1 is another byte 1, then a byte 1 is included in the byte sequence.
If the byte following a byte 1 is any other byte, then both the byte 1 and the following byte are included in the byte sequence.
All other bytes are included in the byte sequence until an unescaped byte 0 is reached.

All passage of NTSBs as parameters to or return values from the procedures described in this document must include the terminating zero.  The null terminator is added when encoding and discarded when decoding.

## Low Level I/O

This module provides low level procedures for reading and writing [SPaDE](../docs/tlad001.md#spade) native repositories as sequences of null terminated byte sequences held in linear binary files.
It also operates a byte sequence cache, which is an array of byte sequences in the order in which they occur in the file, complemented by and efficient means of retrieving the sequence number of a byte sequence already in the cache.

When reading a repository, the entire file is read and the byte sequences are stored in the cache and associated with their sequence numbers (indices into the array).
When writing a repository, byte sequences are first sought in the cache of sequences already in the file.
If the sequence is found in the cache, it is not written to the file and its sequence number is returned.
If the sequence is not found in the cache, it is allocated the next sequence number, written to the file and also stored in the cache.
When appending to an existing repository, byte sequences are written to the end of the file (if not already present) and also stored in the cache.
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

### Open new repository for writing

The file should be opened in append mode, so that new byte sequences written to the repositoryare are added to the end of the file (which will be empty when creating a new repository).

A new empty byte sequence cache should be created.

In order to provide for variations in the SPaDE native repository format which may arise in future, the open new repository procedure will take as arguments a version number.
When creating a new respository, the version number will be written as the first byte sequence in the file.
The current version number is 1 and is written as a null terminated byte sequence representing the integer 1.

This will also be the first entry in the byte sequence cache, and will be elegible for use whenever the version number is required in the repository for whatever purpose.

### Open existing repository for reading

A new empty byte sequence cache should be created for this repository.
The file should then be opened for reading, and the entire repository read and cached using the procedure described below.

### Open existing repository for appending

The file must first be opened for reading to read and cache the entire repository, unless it has already been opened for reading and the cache has not been cleared since then.
The file should then be closed and opened in append mode, so that new byte sequences written to the repository are added to the end of the file.

Upon opening for append, the procedure must verify that the current file size matches the size of the file when it was last read (i.e., the end of the cached data).
If the file size has changed, it indicates that the repository has been modified by another process, and the cache is stale.
In this case, the repository should be closed re-opened in read mode and cached before re-opening in append mode.
If it fails again, an error should be raised.

### Close repository

This would only be called after writing or appending to a repository, or in the prelude to opening an existing repository for appending.
The file should be closed.
The cache should remain available for further use, as is required after reading an existing repository preparatory to appending new byte sequences to it.

### Read byte sequence from repository

This procedure reads the next null terminated byte sequence from the repository file, decodes it into a byte sequence, adds it to the cache, and returns both the byte sequence and its sequence number (index into the cache).

### Write byte sequence to repository

This procedure takes as argument a byte sequence to be written to the repository file.
It first checks whether the byte sequence is already present in the cache.
If it is present, its sequence number (index into the cache) is returned without writing anything to the file.
If it is not present, it is added to the cache at the next available index, written to the end of the file in null terminated form, and its sequence number is returned.

### Retrieve sequence number from cache by byte sequence

This procedure takes as argument a byte sequence and returns its sequence number (index into the cache) if it is present in the cache, and an indication that it is not present if that is the case.
It is for use prior to writing a byte sequence to the repository, to determine whether it is already present and need not therefore be written again.

The values of these two forms are to be returned after each read or write operation.

In order to support these functions, open append will only be allowed when a file has already been opened for reading, and is positioned at the end of the file, so that file position and sequence count are properly maintained.

## J-Expressions

J-expressions are the way in which JSON is represented in SPaDE native repositories.
It is intended that a SPaDE repository can be read as a JSON value, in which directory or folder are given as JSON objects.
The low level I/O is simply intended as an efficient means of storing and retrieving J-expressions in a linear file.

### First Account of the Representation of JSON as J-expressions

A J-expression is an NTBS in a SPaDE Repository.

A module will be provided for reading and writing J-expressions using the low level I/O and encoding/decoding modules.
These J-Expressions are represented using null terminated byte sequences as follows:

Every byte sequence in a SPaDE native repository represents a J-expression.
It does so as a sequence of NTBS in which the byte sequences have the following significance.
The first NTBS indicates the type of J-expression represented, and the remainder give the content of the J-expression.

The signficance of the type code is as follows:

- 0 and 1 are not used to sidestep escaping.
- 2 indicates Nil (which is an empty JSON object).
- 3 is a proper JSON object (which adds a key/value pair to a JSON Object).
- 4 is a key/value pair
- 5 is a JSON array
JSON Objects are represented as lists 
If the first NTBS is a single byte with value 2, the J-expression is Nil which represents an empty object ()

There are two kinds of element in JSON, those which are atomic (i.e. have no JSON parts) and those which are composite (i.e. have JSON parts).

The structured parts are Objects and Arrays.
The atomic parts are Strings, Numbers, Booleans and Null.

- Object: { "key": value, ... } — keys are double-quoted strings; members are comma-separated; order is preserved in practice but not semantically significant.
- Array: [ value, value, ... ] — values are comma-separated; order is significant.
- String: double-quoted, UTF-8 text with escapes (e.g., \", \\, \n, \u1234).
- Number: like JavaScript numbers; no leading + or leading zeros (unless the number is zero); supports exponent (1.2e-3).
Whitespace: optional around punctuation.
Top-level: a single value (commonly an object or array).
GPT-5.1-Codex-Max • 1x

Each J-expression is either Nil, an atom (a null terminated byte sequence) or a CONS cell (pairs of pointers to (sequence numbers of) J-expressions).
Each such J-expression will be represented in the linear file as a single null terminated byte sequence, which when decoded by elimination of escapes would yield a sequence of one two or three null terminated byte sequences.
The first sequence indicates the type of J-expression represented, and the remainder give the content of the J-expression.
The first byte sequence is a single byte (plus null terminator), (*t*), with value 2, 3 or 4, which indicates whether the J-expression is Nil, an atom, or a CONS cell respectively, and also inducates how many further byte sequences follow it in the representation of the J-expression (*t-2*).

After decoding, the first sequence will be a single byte giving the type of J-expression it represents.
If the first byte is 2, the J-expression is Nil, and there are no further byte sequences in the representation.
This is only used to terminate the represetation of objects as lists.
If the first byte is 3, the J-expression is an atom, and the following null terminated byte sequence represents the atom itself.
If the first byte is 4, the J-expression is a CONS cell, and the two subsequent null terminated byte sequences are the sequence numbers of the two J-expressions which are the CAR and CDR of the CONS cell.

Pointers to J-expressions are represented by the sequence number of the null terminated byte sequence representing the expression in the repository.
The module will provide procedures for reading and writing J-expressions to and from the repository file, using the low level I/O and encoding/decoding modules.

The procedures required are:

1. [Write Nil J-expression](#write-nil-j-expression)
2. [Write atom J-expression](#write-atom-j-expression)
3. [Write CONS cell J-expression](#write-cons-cell-j-expression)
4. [Read J-expression](#read-j-expression)

 As a further convenience, the J-expression module will operate a stack for writing J-expressions in the following way:

- the stack is a pointer stack on which sequence numbers of J-expressions written to the repository are held.
- a push operation is provided for Nil and one for Atoms which write to the file (if necessary) and push the sequence number to the stack.
- a cons operation writes to the file a Cons cell whose pointers are the top two elements off the stack, and replaces those two elements with a single pointer which is the sequence number of the Cons cell.

 So we have:

5. [Push Nil](#push-nil)
6. [Push Atom](#push-atom)
7. [Stack Cons](#stack-cons)

### Write Nil J-expression

This procedure writes a Nil J-expression to the repository file.
It creates a null terminated byte sequence representing the J-expression and writes it to the file, returning its sequence number

### Write atom J-expression

This procedure writes an atom J-expression to the repository file.
It takes a byte sequence which is the value of the atom, creates a null terminated byte sequence representing it as an J-expression and writes it to the file (unless already in the cache) returning its sequence number.

### Write CONS cell J-expression

This procedure writes a CONS cell J-expression to the repository file.
It takes two byte sequences numbers which are the CAR and CDR of the CONS cell and must already be in the cache, creates a null terminated byte sequence representing the J-expression and if new writes it to the file, otherwise retrieves its sequence number from the cache.
The sequence number is then returned.

### Read J-expression

This procedure extracts an J-expression from the cache.
It decodes a byte sequence in the cache given its sequence number into an J-expression and returns it.
The J-expression is represented as either:

- Nil
- An atom byte sequence
- A tuple of sequence numbers representing the elements of a CONS cell

### Push Nil

Write Nil, then push the sequence number to the stack.

### Push Atom

Write Atom, then push the sequence number to the stack.

### Stack CONS

Write CONS of top two stack items to the repo and replace them on the stack with the resulting sequence number.

### Append List

Take a list of J-expression sequence numbers and append them to the J-expression whose sequence number is at the top of the stack, replacing that item.
Take the first element off the list, push it to the stack, then CONS the top two items.
Repeat until the list is empty.

## HOL Terms

This module provides procedures for reading and writing HOL types and terms as J-expressions, following the structure defined in [krdd002.md](krdd002.md).
These structures are represented as lists (J-expressions) where the first element is a "Kind Atom" identifying the node type.
The Kind Atom is a single atom containing two null-terminated byte sequences: the *Kind* and the *Manner*.

### Names

Names are represented as single atoms containing a sequence of null-terminated byte strings.
The first byte string represents a numerical shift (up the hierarchy), and subsequent strings represent the path elements.

**Procedures:**

1. **Write Name**: Takes a shift integer and a list of path byte strings. Encodes them into a single atom and writes it. Returns sequence number.
2. **Read Name**: Takes a sequence number. Decodes the atom into a shift integer and list of path strings.

### Types

Types are represented with Kind="Type".
There are two manners:

1. **Type Variable** (Manner="Var"): `Name x Arity`
2. **Type Construction** (Manner="Cons"): `Name x Type list`

**Procedures:**

1. **Write Type Variable**: Takes sequence numbers for Name and Arity (integer). Writes `(Type.Var, Name, Arity)`.
2. **Write Type Construction**: Takes sequence numbers for Name and a list of Types. Writes `(Type.Cons, Name, TypeList)`.
3. **Read Type**: Reads an J-expression. Dispatches based on Manner to return a Type object.

### Terms

Terms are represented with Kind="Term".
There are six manners:

1. **Variable** (Manner="Var"): `Name x Type`
2. **Constant** (Manner="Const"): `Name x Type`
3. **Application** (Manner="App"): `Term x Term`
4. **Abstraction** (Manner="Abs"): `Name x Type x Term`

**Procedures:**

1. **Write Term Variable**: Takes Name and Type sequence numbers. Writes `(Term.Var, Name, Type)`.
2. **Write Term Constant**: Takes Name and Type sequence numbers. Writes `(Term.Const, Name, Type)`.
3. **Write Term Application**: Takes two Term sequence numbers. Writes `(Term.App, Term1, Term2)`.
4. **Write Term Abstraction**: Takes Name, Type, and Term sequence numbers. Writes `(Term.Abs, Name, Type, Body)`.
5. **Read Term**: Reads an J-expression. Dispatches based on Manner to return a Term object.

## Repository Structure

This module handles the organizational structure of the repository, including Theories, Folders, and Commits.

### Structures

1. **Parents**: Kind="Parents". List of Theory sequence numbers.
2. **Signature**: Kind="Signature". `(sname x num)list x (sname x Type)list`.
3. **Extension**: Kind="Extension". `Signature x Term`.
4. **Theory**: Kind="Theory". `Parents x Extension list x ContextHash`.
5. **Folder**: Kind="Folder". `(sname x (Theory | Folder))list`.
6. **Commit**: Kind="Commit". `RootFolder x Signature x Metadata`.

**Procedures:**

1. **Write Parents**: Takes list of Theory sequence numbers. Writes `(Parents, TheoryList)`.
2. **Write Signature**: Takes list of (sname, num) and list of (sname, Type). Writes `(Signature, NameNumList, NameTypeList)`.
3. **Write Extension**: Takes Signature and Term sequence numbers. Writes `(Extension, Signature, Term)`.
4. **Write Theory**: Takes Parents, Extension List, and ContextHash sequence numbers. Writes `(Theory, Parents, ExtList, ContextHash)`.
    - **ContextHash**: A byte sequence (Atom) representing the hash of the context defined by this theory.
5. **Write Folder**: Takes list of (sname, Item) pairs. Writes `(Folder, ItemList)`.
6. **Write Commit**: Takes RootFolder sequence number, Signature (Atom or Nil), and Metadata (Atom). Writes `(Commit, RootFolder, Signature, Metadata)`.
    - **RootFolder**: The sequence number of the new top-level folder of the repository.
    - **Signature**: An optional digital signature of the commit (e.g., signing the hash of the RootFolder and Metadata).
    - **Metadata**: An atom containing commit information (e.g., author, timestamp, description).
7. **Read Structure**: Generic reader or specific readers for each type.

## Repository Updates

This section describes the procedure for performing an "edit" to the repository.
Since the repository is a WORM (Write Once Read Many) structure, existing nodes cannot be modified.
An update is performed by appending new versions of modified nodes and propagating the changes up to the root.

### The Update Cycle

1. **Open for Append**: Open the repository in append mode (verifying cache integrity).
2. **Write New Content**: Write the new or modified Theories/Items to the repository.
3. **Bubble Up**:
    - Identify the path from the modified item to the root.
    - For each folder in the path (bottom-up):
        - Create a new version of the folder containing the new sequence number of the modified child (and existing sequence numbers of unchanged children).
        - Write the new folder to the repository.
4. **Create Commit**:
    - Create a `Commit` structure pointing to the new Root Folder sequence number.
    - Include Metadata (author, message).
    - (Optional) Generate a signature for the commit and include it.
    - Write the `Commit` to the repository.
5. **Update Version List**:
    - The physical end of the repository file represents a list of versions.
    - The new `Commit` is effectively consed onto the existing list of versions (or becomes the new head of the list).
    - (Note: The specific mechanism for linking the new commit to the previous list depends on the top-level file structure defined in `krdd002.md`, typically ending with a Cons cell linking the new Commit to the previous list head).
