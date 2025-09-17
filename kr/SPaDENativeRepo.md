# The SPaDE Native Repository

The SPaDE Native Repository is a specific concrete representation of a subtree of the hierarchic repository of declarative knowledge envisaged by the SPaDE project.

In this document a layered presentation of the structure of that repository is given, from the bottom up.
For the sake of logical coherence, this is a versioned WORM repository, ensuring that for every theorem the context in which it was proved is preserved and can be reconstructed.
Amendments to the content of the repository create new versions, leaving prior versions intact, and theorems are preserved as valid in a specific context, requiring new proofs if the context is changed.

The layers are as follows:

1. *A linear sequence of byte sequences*.  These will in practice often be UTF-8 character strings, but may be arbitrary byte sequences.  It is intended that the SPaDE system be compatible with repositories which do not use UNICODE character sets, and which may incorporate binary data, so the entire encoding of the repository avoids any assumptions about or use of character sets.
Linear sequences of bytes are found at multiple levels, not only in this base layer, and the method of encoding is the same at all levels.

2. Coded in that linear array *a general representation of tree structures*, represented in the simplest way as atoms, the empty list NIL, and binary nodes (CONS cells) which add a head to a list.

3. Coded in that tree structure *a representation of a heirarchy of contexts or theories*, each of which introduces various names by including them in a signature indicating what type of value they denote, and providing a constraint which assigns meaning to the names.
Metadata which might be included in theories will not be explicitly incorporated into theories at this stage, but are expected to form the subject matters of separate theories which will refer back to the theory to which they relate, so that the content of a theory is strictly limited to the signatures and constraints which define the context.
Caches of theorems will be maintained by the deductive intelligence subsystem, along with neural net heuristics specific to logical contexts.
These will also be stored in separate theories which refer back to the contexts in which the theorems were proved, and to which the heuristics apply.

## Layer 1: A Linear Sequence of Byte Sequences

In this sequence of sequences, the sequences are represented as null-terminated byte sequences, allowing for inclusion of the zero byte by using binary 1 as an escape character.
Note that though these byte sequences will often be UTF-8 character strings, they are not restricted to that format, and may be arbitrary byte sequences.
Since the intention is that this will be written and read linearly, the position of a sequence in the file may be represented by counting the sequences and using that count as an index.
In some places sucha sequence of bytes may be used to represent a number, and may then be thought of as a base 256 number, with the most significant byte first ("big endian").

## Layer 2: A Tree Structure

The tree structure is represented by using the byte sequences to code the three kinds of node required, namely atoms, NIL and binary nodes (CONS cells).
The first byte of each sequence identifies the kind of node, and is binary 2 for NIL, 3 for atoms and 4 for CONS cells.

### NIL

NIL is represented by a single byte sequence consisting of the byte 2 (followed by the null terminator)
For a minor space saving, the first byte sequence in each SPaDE repository file will be NIL, so that the index of NIL is always 0.

### Atoms

Atoms are represented by a sequence beginning with the byte 3 followed by the (null terminated) byte sequence which is the value of the atom.

### CONS Cells

CONS cells consist of binary 4 followed by two null terminated byte sequences interpreted as positions in the repositories sequence of sequences.
These are the positions of the CAR and CDR of the CONS cell in the linear sequence of byte sequences.
A pointer to NIL will always be the empty byte sequence (index 0).
Pointers are represented as base 256 numbers, with the most significant byte first ("big endian"), the number being the index of the target sequence in the linear sequence of sequences, starting from 0 which will always be the position of NIL.

## Layer 3: The Hierarchies of Names and Contexts

From here on in structures are represented as S-expressions using the tree structure of layer 2.

This specification will not give the well-formedness conditions for these structures, but will be exclusively concerned with the representation of these structures as S-expressions.
This primarily consists in enumerating the various kinds of node which will be used in the representation, and describing the components compounded by the structure.

Each node will be a list formed using CONS cells of which the first element is an atom identifying the kind of node, and the remaining elements are the components of that node.
That atom will consist of two null terminated byte strings of which the first is the kind of entity constructed and the second the manner of construction.

These are:

1. Type
  1.1 Type variable: Name x Arity
  1.2 Type construction: Name x Type list
2. Term
  2.1 Variable: Name x Type
  2.2 Consta;nt: Name x Type
  2.3 Application: Term x Term
  2.4 Abstraction: Name x Term
  2.5 Literal: S-expression
  2.6 Relocation: Name x Term
3. Parents: Theory list
4. Signature: (Type x num)list x (sname x Type)list
5. Extension: Signature x Term
6. Theory: Parents x Extension list x SignedHash
7. Folder: (sname x (Theory | Folder))list


In the above each construction is either an atom or a list, but lists are mostly short finite lists of components and are shown as if tuples using the "x" operator.
This is purely a typographical convenience.

First however, we need to know what is a name, and the interrelationship of names in different logical contexts.
In SPaDE repositories there are two distinct but interrelated hierarchical structure.

### The Name Hierarchy

The first is a hierarchy of names which provides a global namespace in which names are allocated to contributors in such a way that the names allocated to distinct contributors are distinct, enabling different contributions to be coherently combined.
The meanings assigned to these names are subject to amendment, and the name spaces are therefore versioned, so that the logical context for any theorem can be reconstructed.
The hierarchy of names is built using collections which may generally be thought of as folders or directories, at the lowest level of which appear *theories*, which determine a logical context by extension to previously defined contexts.
Within a SPaDE respository there will be a versioned hierarchy of folders containing theories.
Above that level, to enable reference to contexts in other repositories, there will be a further hierarchy of folders or directories, which corresponds (as far as earthly repositories are concerned) to the structure of URL's.

In order for this hierarchy to be open ended, to admit continuous expansion through other planets, star systems and galaxies, all name references will be relative, and access to larger domains will be possible through higher levels of the hierarchy.

Though in principle this makes it possible for developments to take place in the context of the entire known subsystems of the cosmic namespace, we neverthess want to enable each development to take place in a context curated for that development, including only the vocabulary for theories on which the development depends.
This is essential to enable appropriate focus, and for the operation of the focal AI methods which are to be used in the deductive intelligence subsystem.

### The Context Hierarchy

The second hierarchy is that of contexts.
A context is formed by extending one or more prior contexts (which may be called *parents*)by adding new names and constraints on those names.
Such references to prior contexts may be to contexts in the same repository.
They will always be to specific versions of those contexts, so that the context in which any theorem was proved can be reconstructed.
Such a reference can be either symbolic or by pointer to the position in the SPaDE Native Repository of the context being referred to.
Both of these methods will be used, and the integrity of reference to contexts will be ensured by the use of checksums or hashes and digital signatures to verify the content of each logical context in which any theorem has been derived.

### Names

Names will therefore be presented as relative paths, navigating structures which are or can be understood as directories or folders in a hierarchical knowledge repository.
Such a relative path will consist of a single numerical shift to a higher level in the hierarchy, together with a path to a specific defined name in a repository, local or remote.
Each element in the path will be a byte sequence which may or may not be a UTF-8 character string.

These will be encoded in a single atom interpreted as a sequence of null terminated byte sequences.

### Types

A type is either
