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

## Layer 3: A Hierarchy of Contexts or Theories

This of course, is the complicated bit and likely to evolve as we proceed.
We can do this by stages, since the representation of types and terms is relatively straightforward and must be addressed first.

First however, we need to know what is a name.

### Names

The idea that we can have shared widely distributed repositories of declarative knowledge requires that we can have a shared universe of names divided among potential contributors, ensuring that merging contributions does not compromise logical consistency.
This requires an administrative structure which can allocate namespaces to contributors, and ensure that these namespaces are disjoint.

URL's and URI's already accomplish this through the registration of domain names, though this is limited to planet Earth, and will need adaptation to encompass other planets, stars and galaxies.
For that purpose it is natural to anticipate higher levels to the existing domain name system within which our existing domain names are nested.
A further difficulty in such a naming scheme, even if only for planet Earth, is that the names are long and cumbersome.

To deal with these two problems, names in SPaDE will be relative, so that references to names defined locally will be less cumbersome.
The problem of name complexity can also be mitigated in the repository by defining local names as synonyms for cumbersome remote references.
It is also open to software presentating formal materials for human consumption to adopt further mitigations in those presentations (SPaDE does not provide such interfaces, delivering functionality exclusively through MCP servers).

Names will therefore be presented a relative paths, navigating structures which are or can be undestood as directories or folders in a hierarchical knowledge repository.
Such a relative path will consist of a single numerical shift to a higher level in the hierarchy, together with a path to a specific defined name in a repository, local or remote.
Each element in the path will be a byte sequence which may or may not be a UTF-8 character string, optionally followed by a version number, which will usually be required in a reference to a remote repository.

**[There is a problem here in ensuring that the correct version of a constant is located, which concerns when it is necessary to identify version numbers in the path.
A protective measure to ensure integrity in case I get that wrong will be the use of checksums or hashes to verify the content of each logical context in which any theorem has been derived.]**

This is a particularly tricky part of the design and will benefit from further thought and discussion.
The lower levels of the repository structure are intended to replicate the behaviour of functional programming languages when editing list structures.
When this happens, the original structure remains unchanged, and a new structure is created which shares as much of the original as possible though links in CONS cells to the original structure.

At this level integrity seems straightforward.
However, in the structures which are intended there are two further hierarchies as follows.

There is the name hierarchy in which names of constants are fixed by the descent through a hierarchy of folders or directories, each of which may have a version number.
