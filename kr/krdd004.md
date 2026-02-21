# Detail description of Procedures for SPaDE Native Repository I/O

This document describes the procedures for reading and writing [SPaDE](../docs/tlad001.md#spade) native repositories in sufficient detail to guide implementation.

In first drafts of this document the procedures defined are those necessary to write a [SPaDE](../docs/tlad001.md#spade) repository from scratch, and to read an existing repository into a suitably structured representation.

Some of the detail will depend upon the language in which the procedures are implemented.
Where possible, pertinent differences will be highlighted.
Only two languages are currently under consideration, SML (for HOL4 and ProofPower HOL implementations) and Python (for MCP server implementations).
The former are only intended for the export of theory hierarchies from existing HOL ITP systems into [SPaDE](../docs/tlad001.md#spade) repositories, while the latter are intended for use in delivering the broader functionality of [SPaDE](../docs/tlad001.md#spade) through the logical kernel, deductive intelligence and MCP server subsystems.
Python may also to be used in due course for export of theories from Lean.

It is possible that access to non-SPaDE repositories will not be undertaken by writing from their custodians to a SPaDE repository, but via a simpler export directly to SPaDE facilities implemented in Python.
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
- [S-Expressions](#s-expressions)
- [HOL Types and Terms](#hol-types-and-terms)
- [Repository Structure](#repository-structure)

## Encoding/Decoding

The SPaDE native repository is a sequence of null terminated byte sequences (NTBS).
It is necessary to have procedures for encoding arbitrary byte sequences as null terminated byte sequences, and for decoding such sequences back into arbitrary byte sequences.
Multiple NTBS can be appended then converted into a single NTBS which may then be styled an NTBSS.
In fact, all the NTBS in a SPaDE repository are NTBSS, since at the second layer they are all used to represent S-expressions which are sequences of NTBS.

This module provides procedures for encoding and decoding null terminated byte sequences and for appropriate conversions of a small number of data types, as byte sequences.

The data conversions required are as follows (in all cases conversions are required in both directions):

- byte sequences <-> NTBS

  Encoding a byte sequence as a null terminated byte sequence, and decoding a null terminated byte sequence into a byte sequence.

- NTBS list <-> NTBSS

  This is just applying the NTBS encoding to the concatenation of the individual NTBS.

- byte sequences <-> strings

  Attempt to decode as utf-8 (strict); if successful use the resulting utf-8 string, otherwise use a JSON object with a single key-value pair with the key "hexbytes" and a value consisting of the hexadecimal representation (beginning "0x") of the byte sequence as a string.

- byte sequences <-> integers

  These are for the representation of integers as byte sequences in big-endian base 256 form.
  The conversion is used primarily for the sequence number of byte sequences in the repository file, and for any other integer values represented in the repository.

When encoding integers, the integer is first represented as a sequence of bytes in big-endian order base 256, and then that byte sequence is encoded as a null terminated byte sequence using the procedure for encoding byte sequences.
Decoding first decodes a null terminated byte sequence into a byte sequence, and then interprets that byte sequence as a big-endian representation of an integer.

The final provision allows that a single null terminated byte sequence can be used to represent a list of such sequences.
This is achieved by appending the null terminated byte strings and then encoding that as a single null terminated byte sequence, using the previously described procedure for encoding byte sequences.
The null terminatory of the individual byte sequences will then be escaped during encoding and restored when decoding.

The coding of byte sequences into null terminated form is as follows:

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

All passage of NTBS as parameters to or return values from the procedures described in this document must include the terminating zero.  The null terminator is added when encoding and discarded when decoding.

## Low Level I/O

This module provides low level procedures for reading and writing [SPaDE](../docs/tlad001.md#spade) native repositories as sequences of null terminated byte sequences held in linear binary files.
It also operates a byte sequence cache, which is an array of byte sequences in the order in which they occur in the file, complemented by an efficient means of retrieving the sequence number of a byte sequence already in the cache.

All byte sequences in a repository and in the cache are in null terminated form with escapes as described above, and all the interfaces at the low level I/O expect or deliver byte sequences in that form.

When reading a repository, the entire file is read and the byte sequences are stored in the cache and associated with their sequence numbers (indices into the array).
When writing a repository, byte sequences are first sought in the cache of sequences already in the file.
If the sequence is found in the cache, it is not written to the file and its sequence number is returned.
If the sequence is not found in the cache, it is allocated the next sequence number, written to the file and also stored in the cache.
When appending to an existing repository, byte sequences are written to the end of the file (if not already present) and also stored in the cache.
Links within the repository are represented using these sequence numbers (and will always point backwards since this is a WORM repository).

Reflecting the distributed nature of the diasporic repository, the low-level I/O facility must be capable of opening and operating on multiple repositories simultaneously.
For example, a theory in one (local) repository may designate as parents theories residing in other (possibly remote) repositories.
To support this, the procedures in this module will operate on a repository handle.
Each handle encapsulates a file handle and a dedicated byte sequence cache for that specific repository.

The operations required are:

1. [Open new repository for writing](#open-new-repository-for-writing)
2. [Open existing repository for reading](#open-existing-repository-for-reading)
3. [Open existing repository for appending](#open-existing-repository-for-appending)
4. [Close repository](#close-repository)
5. [Read byte sequence from repository](#read-byte-sequence-from-repository)
6. [Write byte sequence to repository](#write-byte-sequence-to-repository)
7. [Retrieve byte sequence from cache by sequence number](#retrieve-byte-sequence-from-cache-by-sequence-number)
8. [Retrieve sequence number from cache by byte sequence](#retrieve-sequence-number-from-cache-by-byte-sequence)

### Open new repository for writing

The file should be opened in append mode, so that new byte sequences written to the repository are added to the end of the file (which will be empty when creating a new repository).

A new empty byte sequence cache should be created.

In order to provide for variations in the SPaDE native repository format which may arise in future, the open new repository procedure will take as arguments a version number.
When creating a new repository, the version number will be written as the first byte sequence in the file.
The current version number is 1 and is written as a null terminated byte sequence representing the integer 1.

This will also be the first entry in the byte sequence cache, and will be eligible for use whenever the version number is required in the repository for whatever purpose.

### Open existing repository for reading

A new empty byte sequence cache should be created for this repository.
The file should then be opened for reading, and the entire repository read and cached using the procedure described below.
It is necessary to read the entire repository in order to identify the start of the last NTBS in the file, which is the head of the last commit in the repository, from which the structure of the repository can be reconstructed.

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

### Retrieve byte sequence from cache by sequence number

This procedure takes as argument a sequence number (index into the cache) and returns the corresponding byte sequence from the cache, in the process decoding it from null terminated form.

### Retrieve sequence number from cache by byte sequence

This procedure takes as argument a byte sequence and returns its sequence number (index into the cache) if it is present in the cache, and an indication that it is not present if that is the case.
It is for use prior to writing a byte sequence to the repository, to determine whether it is already present and need not therefore be written again.

The values of these two forms are to be returned after each read or write operation.

In order to support these functions, open append will only be allowed when a file has already been opened for reading, and is positioned at the end of the file, so that file position and sequence count are properly maintained.

## S-Expressions

The NTBS in a SPaDE repository are used to represent S-expressions, general purpose list structures which are used to represent the content of the repository, and in particular the theories and their components.

Exactly how S-expressions are represented in memory after reading from or before writing to the repository depends upon the context and the implementation language.
The main functionality of SPaDE is implemented using a repository manager implemented in Python, which provides access to SPaDE native repositories for the deductive kernel, deductive intelligence and MCP server subsystems.
For this purpose a type of S-expressions will be defined in Python, and the procedures for reading and writing S-expressions to and from the repository will operate on that type, converting values between S-expressions and their NTBS representations as necessary.

The other three subsystems are given access to the relevant context as S-expressions extracted from one or more SPaDE repositories, or other sources of declarative knowledge mediated by specialised procedures presenting that knowledge as if it were read from a SPaDE native repository.

Alternatively the import of knowledge will be undertaken by facilities which read from the source repository and write to a SPaDE repository, using structures and languages appropriate to the source repository, and the S-expression module will be used only for the reading and writing of S-expressions to and from the SPaDE repository, and not for the intermediate representation of the knowledge in the source repository.

There are three levels at which similar structures may be represented as S-expressions:

1. As an NTBS in the SPaDE native repository file, possibly linked to other NTBS via sequence numbers.
2. As a S-expression, in which an NTBS has its top level structure decoded, but lower level structures (i.e. the two elemenst of a CONS cell) are given a references NTBS in a repository file.
3. As a fully decoded S-expression, in which all the NTBS are decoded into their corresponding structures, and all links to other NTBS are replaced by the corresponding structures.

The structure of S-expressions and the manner in which they are used is influenced by the fact that a SPaDE native repository is a WORM repository, and the need to minimise replication of information in successive versions of an structure in the repository.
In the case of folder or folder-like structures such as theories, the most frequent changes are likely to be the addition of new items, and to avoid unnecessary replication of the unchanged items, the structure of the folder is represented as a sequence of additions to an initially empty folder, with each addition being a CONS cell containing the item being added and a reference to the previous state of the folder.
One may think of this as adding an item to the end of a list, but CONSing an item onto a list is normally thought of as adding to the head or front of the list.
So it will generally be the case that the list structures in the SPaDE repository are in reverse order, and are accessed from the end of the list rather than the beginning.

It is intended that a SPaDE repository as a whole can be read as an S-expression.
The low level I/O is simply intended as an efficient means of storing and retrieving these S-expressions in a linear file (as a WORM repository).

Apart from the folder-like structures the Lists in the repository as read in the more traditional order, will be used as tuples of which the first element is a numeric code indicating the syntactic constructor of item represented, uniquely identifying a production in the abstract syntax of HOL, and the remaining elements refer to the parameters required by that constructor (the relevant abstract syntax may be found in [krad001.md](krad001.md)).

### First Account of the SPaDE Native Representation of S-expressions

An S-expression is an NTBS in a SPaDE Repository.

A module will be provided for reading and writing S-expressions using the low level I/O and encoding/decoding modules.
These S-Expressions are represented using null terminated byte sequences as follows:

Each S-expression is either Nil, an atom (a null terminated byte sequence) or a CONS cell (pairs of pointers to (sequence numbers of) S-expressions).
Each such S-expression will be represented in the linear file as a single null terminated byte sequence, which when decoded by elimination of escapes would yield a sequence of one two or three null terminated byte sequences.
The first sequence indicates the type of S-expression represented, and the remainder give the content of the S-expression.
The first byte sequence is a single byte (plus null terminator), (*t*), with value 2, 3 or 4, which indicates whether the S-expression is Nil, an atom, or a CONS cell respectively, and also indicates how many further byte sequences follow it in the representation of the S-expression (*t-2*).

After decoding, the first sequence will be a single byte giving the type of S-expression it represents.
If the first byte is 2, the S-expression is Nil, and there are no further byte sequences in the representation.
If the first byte is 3, the S-expression is an atom, and the following null terminated byte sequence represents the atom itself.
If the first byte is 4, the S-expression is a CONS cell, and the two subsequent null terminated byte sequences are the sequence numbers of the two S-expressions which are the CAR and CDR of the CONS cell.

Pointers to S-expressions are represented by the sequence number of the null terminated byte sequence representing the expression in the repository.
The module will provide procedures for reading and writing S-expressions to and from the repository file, using the low level I/O and encoding/decoding modules.

The procedures required are:

1. [Write Nil S-expression](#write-nil-s-expression)
2. [Write atom S-expression](#write-atom-s-expression)
3. [Write CONS cell S-expression](#write-cons-cell-s-expression)
4. [Read S-expression](#read-s-expression)

    As a further convenience, the S-expression module will operate a stack for writing S-expressions in the following way:

    - the stack is a pointer stack on which sequence numbers of S-expressions written to the repository are held.
    - a push operation is provided for Nil and one for Atoms which write to the file (if necessary) and push the sequence number to the stack.
    - a cons operation writes to the file a Cons cell whose pointers are the top two elements off the stack, and replaces those two elements with a single pointer which is the sequence number of the Cons cell.

    So we have:

5. [Push Nil](#push-nil)
6. [Push Atom](#push-atom)
7. [Stack Cons](#stack-cons)

### Write Nil S-expression

This procedure writes a Nil S-expression to the repository file.
It creates a null terminated byte sequence representing the S-expression and writes it to the file, returning its sequence number.
Apart from the first time, this will simply be returning the sequence number of the first time, since the same byte sequence will be used for all Nil S-expressions, and will be cached after the first write.

### Write atom S-expression

This procedure writes an atom S-expression to the repository file.
It takes a byte sequence which is the value of the atom, creates a null terminated byte sequence representing it as an S-expression and writes it to the file (unless already in the cache) returning its sequence number.

### Write CONS cell S-expression

This procedure writes a CONS cell S-expression to the repository file.
It takes two byte sequences numbers which are the CAR and CDR of the CONS cell and must already be in the cache, creates a null terminated byte sequence representing the S-expression and if new writes it to the file, otherwise retrieves its sequence number from the cache.
The sequence number is then returned.

### Read S-expression

This procedure extracts an S-expression from the cache.
It decodes a byte sequence in the cache given its sequence number into an S-expression and returns it.
The S-expression is represented as either:

- Nil
- An atom byte sequence
- A pair of sequence numbers representing the CAR and CDR of a CONS cell

### Push Nil

Write Nil, then push the sequence number to the stack.

### Push Atom

Write Atom, then push the sequence number to the stack.

### Stack CONS

Write CONS of top two stack items to the repo and replace them on the stack with the resulting sequence number.

### Append List

Take a list of S-expression sequence numbers and append them to the S-expression whose sequence number is at the top of the stack, replacing that item.
Take the first element off the list, push it to the stack, then CONS the top two items.
Repeat until the list is empty.

## HOL Types and Terms

Though it is natural to think of the repository structure as consisting of more than one additional layer above S-expressions, in practice all the structures required for representing HOL terms and types, and the repository structure itself, can be mapped into S-expressions in a uniform way.

They are all represented as S-expressions which are arrays of which the first element is the name of a constructor.

At this level the name of the constructor can be used, which in the NTBS representation of the array would be given as the sequence number of the atom representing the string in the repository.

The best way to describe these constructors is as an abstract syntax, even though their substrate is J-expressions which are not typed.
In order to avoid confusion of these with the types in the object language of interest, we will call these categories (abstract syntax categories).

The categories are as follows, with the constructors and arities indicated for each category:

- SimpleName
  - Sname: string
- RelativeName
  - Rname: int x string array
- Type
  - Tvar: Sname
  - Tcon: Rname x Type array
- Term
  - Var: Sname x Type
  - Const: Rname x Type
  - App: Term x Term x Type
  - Abs: Sname x Type x Term x Type
- Sequent

The abstract syntax associates with each constructor a category, and the categories of the parameters which it requires.

The required constructors, together with the types of the parameters which they require are as follows:

- Tvar: name
- Tcon: name x type list

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
3. **Read Type**: Reads an S-expression. Dispatches based on Manner to return a Type object.

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
5. **Read Term**: Reads an S-expression. Dispatches based on Manner to return a Term object.

## Repository Structure

This module handles the organizational structure of the repository, including Theories, Folders, and Commits.

- Seq: Term array x Term
- Theorem
  - Theorem: Sequent x Chash x CSign
- Signature
- Theory
- Folder

A folder is represented as a JSON object mapping names to either Theories or Folders. To maintain the integrity of the repository, cryptographic hashes are used in the top-level folder which is a folder of commits to the repository representing successive versions of the repository.  For this reason, folders associate names with pairs of which the first links to a cryptographic hash and the second is the top folder of the new commit. The cryptographic hash element will link to null for all non-top-level folders.  Otherwise it will be a hash formed on the NTBS from the last commit to that of the folder now being committed and linked to by the new commit.

This will include the hash of the previous top-level folder, so that the entire history of the repository is captured in the chain of commits. This same cryptographic hash will be used in the signature of any theorems derived in the contexts being committed.

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
