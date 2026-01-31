# Detail description of Procedures for SPaDE Native Repository I/O

*(version 0.2 in progress:
The central thrust of this change is to change the second layer from an S-expression-like structure, to one more closely aligned with JSON since that is the language with which the SPaDE MCP server will engage with its AGI clients.
Once that is done the remaining layers can be properly described here, and the whole thing coded up in both SML and Python.

TO DO: complete the details of these changes.
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
- [HOL Types and Terms](#hol-types-and-terms)
- [Theories and Folders](#theories-and-folders)

## Encoding/Decoding

The SPaDE native repository is a sequence of null terminated byte sequences (NTBS).
It is necessary to have procedures for encoding arbitrary byte sequences as null terminated byte sequences, and for decoding such sequences back into arbitrary byte sequences.
Multiple NTBS can be appended then converted into a single NTBS which may then be styled an NTBSS.
In fact, all the NTBS in a SPaDE repository are NTBSS, since at the second layer they are all used to represent J-expressions which are sequences of NTBS.

This module provides procedures for encoding and decoding null terminated byte sequences and for appropriate conversions of a small number of data types, as byte sequences.

The data conversions required are as follows (in all cases conversions are requred in both directions):

- byte sequences <-> NTBS

  Encoding a byte sequence as a null terminated byte sequence, and decoding a null terminated byte sequence into a byte sequence.

- NTBS list <-> NTBSS

  This is just applying the NTBS encoding to the concatenation of the individual NTBS.

- byte sequences <-> strings

  Attempt to decode as utf-8 (strict); if successful use the resulting JSON string, otherwise use a JSON object with a single key-value pair with the key "hexbytes" and a value consisting of the hexadecimal representation (beginning "0x") of the byte sequence as a string.

- byte sequences <-> integers

  These are for the representation of positive integers as byte sequences in big-endian base 256 form.
  The conversion is used for the sequence number of byte sequences in the repository file, and for other integer values represented in the repository.
  This is not used for JSON numbers, which are represented as byte sequences of their textual representation.

- JSON numbers <-> byte sequences

  These are represented as their textual representation in ASCII (utf-8) as byte sequences.

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

The file should be opened in append mode, so that new byte sequences written to the repository are are added to the end of the file (which will be empty when creating a new repository).

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

### Retrieve byte sequence from cache by sequence number

This procedure takes as argument a sequence number (index into the cache) and returns the corresponding byte sequence from the cache, in the process decoding it from null terminated form.

### Retrieve sequence number from cache by byte sequence

This procedure takes as argument a byte sequence and returns its sequence number (index into the cache) if it is present in the cache, and an indication that it is not present if that is the case.
It is for use prior to writing a byte sequence to the repository, to determine whether it is already present and need not therefore be written again.

The values of these two forms are to be returned after each read or write operation.

In order to support these functions, open append will only be allowed when a file has already been opened for reading, and is positioned at the end of the file, so that file position and sequence count are properly maintained.

## J-Expressions

J-expressions are the way in which JSON is represented in SPaDE native repositories.
The use of J-expressions is aligned with the use of textual JSON as the protocol for communication between the SPaDE MCP server and its clients, and the use of python JSON objects (as opposed to JSON text) as an intermediary between the binary representation in the SPaDE native repository and the textual representation used in communication and in the SPaDE deductive kernel and deductive intelligence subsystems.

This relationship is further complicated by intended use of the JSON object in python with subexpressions consisting of sequence numbers in the SPaDE native repository, which are to be dereferenced to yield further J-expressions.

So, when a SPaDE native repository is read across the MCP server interface, the following representations of each JSON expression are involved:

1. As an NTBS in the SPaDE native repository file, possibly linked to other NTBS via sequence numbers.
2. As a J-expression, in which an NTBS has its top level structure decoded.
3. As a JSON object in python, in which the J-expression is represented as a python object, with links represented as sequence numbers.

When writing a SPaDE native repository from python JSON objects, the process is reversed:
2. The representation of J-expressions as sequences of null terminated byte sequences in the SPa

It is intended that a SPaDE repository can be read as a JSON value, in which directories or folders are given as JSON objects.
The low level I/O is simply intended as an efficient means of storing and retrieving these J-expressions in a linear file (as a WORM repository).

All the structures required for representing HOL terms and types, and the repository structure itself, will be represented as J-expressions, and this will facilitate communication across the MCP server interface using JSON.

### First Account of the Representation of JSON as J-expressions

A J-expression is an NTBS in a SPaDE Repository.

A module will be provided for reading and writing J-expressions using the low level I/O and encoding/decoding modules.
These J-Expressions are represented using null terminated byte sequences as follows:

Every byte sequence in a SPaDE native repository represents a J-expression, providing the top-level structure of the JSON and pointers to any lower level content where the item is an object or an array.
It does so as a sequence of NTBS in which the byte sequences have the following significance.

The first NTBS indicates the kind of J-expression represented, and the remainder give the content of the J-expression.

The signficance of the kind code is as follows:

- 0 and 1 are not used (to sidestep escaping).
- 2 is an object (which appends a key/value pair to a JSON Object or Null).
- 3 is an array or (n-tuple)
- 4 byte sequence (usually but not necessarily utf-8)
- 5 number
- 6 boolean true
- 7 boolean false
- 8 Null (which also serves as an empty J-expression object).

The remaining NTBS in the representation depend upon the kind of J-expression represented as follows:

- 2 (Object): three following NTBS, all sequence numbers of NTBS, the first of a key the second of a value associated with that key and the third the sequence number of the remainder of the object (or of Null to terminate).
- 3 (Array): the number of following NTBS is the length of the array, each being the sequence number of an NTBS representing a J-expression in the array.
- 4 (byte sequence): the following single NTBS is the byte sequence (once decoded).  The presentation of such sequences in textual JSON is discussed above under Encoding/Decoding.
- 5 (Boolean true): no following NTBS.
- 6 (Boolean false): no following NTBS.
- 7 (Null): no following NTBS.

J-expression Objects are represented in manner similar to LISP lists except that they are always lists of key/value pairs, and so the equivalent of CONS takes three arguments, sequence numbers of the key, the value, and the rest of the object.

There are two kinds of element in J-expressions, those which are atomic (i.e. have no JSON parts, kinds 4-8) and those which are composite (i.e. have JSON parts, kinds 2 and 3).
In J-expressions, the parts are given as sequence numbers of the byte sequences representing those parts in the repository file.
As described above, the number of such parts depends upon the kind of J-expression represented.  For kind 2 there are 3 for kind 3 there as many as the length of the array, for kinds 4 - 8 the value is the following NTBS which is not a link.

The atoms are explicitly represented as byte sequences.

The structured parts are Objects and Arrays.
The atomic parts are Byte sequences, Numbers, True, False and Null.

The textual presentation of these J-expressions as JSON is as follows (but is of little significance here):

- Object: { "key": value, ... } — keys are double-quoted strings; members are comma-separated; order is preserved in practice (but not semantically significant?).
- Array: [ value, value, ... ] — values are comma-separated; order is significant.
- String: double-quoted, UTF-8 text possibly with escapes (e.g., \", \\, \n, \u1234) OR if not valid UTF-8, an object {"hexbytes": "0x..."} where ... is the hexadecimal representation of the byte sequence.
- Boolean: true or false.
- Null: null.
- Number: like JavaScript numbers; no leading + or leading zeros (unless the number is zero); supports exponent (1.2e-3).
Whitespace: optional around punctuation.
Top-level: a single value (commonly an object or array).

Each such J-expression will be represented in the linear file as a single null terminated byte sequence, which when decoded by elimination of escapes would yield a sequence of  null terminated byte sequences.
The first sequence indicates the type of J-expression represented, and the remainder give the content of the J-expression, in the manner described above.

The procedures required are:

1. [Write Null J-expression](#write-null-j-expression)
2. [Write atom J-expression](#write-atom-j-expression)
3. [Write object cell J-expression](#write-object-cell-j-expression)
4. [Read J-expression](#read-j-expression)

    As a further convenience, the J-expression module will operate a stack for writing J-expressions in the following way:

    - the stack is a pointer stack on which sequence numbers of J-expressions written to the repository are held.
    - a push operation is provided for Nil and one for Atoms which write to the file (if necessary) and push the sequence number to the stack.
    - a cons operation writes to the file a Cons cell whose pointers are the top two elements off the stack, and replaces those two elements with a single pointer which is the sequence number of the Cons cell.

    So we have:

5. [Push Null](#push-null)
6. [Push Atom](#push-atom)
7. [Stack Object](#stack-object)
8. [Stack Array](#stack-array)

### Write Null J-expression

This procedure writes a Null J-expression to the repository file.
It creates a null terminated byte sequence representing the J-expression and writes it to the file, returning its sequence number.

### Write atom J-expression

This procedure writes an atom J-expression to the repository file.
It takes a byte sequence which is the value of the atom, creates a null terminated byte sequence representing it as an J-expression and writes it to the file (unless already in the cache) returning its sequence number.

### Write object cell J-expression

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

### Push Null

Write Nil, then push the sequence number to the stack.

### Push Atom

Write Atom, then push the sequence number to the stack.

### Stack object

Write CONS of top three stack items to the repo and replace them on the stack with the resulting sequence number.

### Append List

Take a list of J-expression sequence numbers and append them to the J-expression whose sequence number is at the top of the stack, replacing that item.
Take the first element off the list, push it to the stack, then CONS the top two items.
Repeat until the list is empty.

## HOL Types and Terms

Though it is natural to think of the repository structure as consisting of more than one additional layer above J-expressions, in practice all the structures required for representing HOL terms and types, and the repository structure itself, can be mapped into J-expressions in a uniform way.

They are all represented as J-expressions which are arrays of which the first element is the name of a constructor.

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

-

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

## Theories and Folders

This module handles the organizational structure of the repository, including Theories, Folders, and Commits.

- Seq: Term array x Term
- Theorem
  - Theorem: Sequent x Chash x CSign
- Signature
- Theory
- Folder

A folder is represented as a JSON object mapping names to either Theories or Folders. To maintain the integrity of the repository, crptographic hashes are used in the top-level folder which is a folder of commits to the repository representing successive versions of the repository.  For this reason, folders associate names with pairs of which the first links to a cryptographic hash and the second is the top folder of the new commit. The cryptographic hash element will link to null for all non-top-level folders.  Otherwise it will be a hash formed on the NTBS from the last commit to that of the folder now being committed and linked to by the new commit.

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
    - A commit is accomplished by writing an additional type/value pair to the top level folder.  The type is name of the commit and the value is the value of the repo being committed, normally created