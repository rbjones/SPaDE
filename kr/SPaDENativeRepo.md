# The SPaDE Native Repository

The SPaDE Native Repository is a specific concrete representation of a subtree of the hierarchic repository of declarative knowledge envisaged by the SPaDE project.

In this document a layered presentation of the structure of that repository is given, from the bottom up.
For the sake of logical coherence, this is a versioned WORM repository, ensuring that for every theorem the context in which it was proved is preserved and can be reconstructed.
Amendments to the content of the repository create new versions, leaving prior versions intact, and theorems are preserved as valid in a specific context, requiring new proofs if the context is changed.

The layers are as follows:

1. *A linear sequence of byte sequences*.  These will in practice often be UTF-8 character strings, but may be arbitrary byte sequences.  It is intended that the SPaDE system be compatible with repositories which do not use UNICDE character sets, and which may incorporate binary data.

2. Coded in that linear array *a general representation of a tree structure*, represented in the simplest way as atoms (including NIL), and binary nodes (CONS cells).

3. Coded in that tree structure *a representation of a heirarchy of contexts or theories*, each of which introduces various names by including them in a signature indicating what type of value they denote, and providing a constraint which assigns meaning to the names.
Metadata which might be included in theories will not be explicitly incorporated into theories at this stage, but are expected to form the subject matters of separate theories which will refer back to the theory to which they relate.
Caches of theorems be maintained by the deductive inteligence subsystem, along with neural net heuristics specific to logical contexts.
These will also be stored in separate theories which refer back to the contexts in which the theorems were proved, and to which the heuristics apply.

## Layer 1: A Linear Sequence of Byte Sequences

In this sequence of sequences, the sequences are represented as null-terminated byte sequences, allowing for inclusion of the zero byte using "\" as an escape character.
Note that though these byte sequences will often be UTF-8 character strings, they are not restricted to that format, and may be arbitrary byte sequences.
Since the intention is that this will be written and read linearly, the position of a sequence in the file may be represented by counting the sequences and using that count as an index.

## Layer 2: A Tree Structure

The tree structure is represented by using the byte sequences to code the three kinds of node required, namely atoms, NIL and binary nodes (CONS cells).

### Atoms

Atoms are represented by a sequence beginning with the character "1" followed by the byte sequence which is the value of the atom.

### NIL

We only need one NIL, and it can be dispensed with in favour of a NIL link in CONS cells, so we imagine that NIL is a virtual element which is always the zero'th sequence in the file (though in fact the first sequence in the file has index 1).

### CONS Cells

CONS cells consist of two hexadecimal numbers each preceded by "x".
These are the positions of the car and cdr of the cons cell in the linear sequence of byte sequences.
Thus a CONS cell with car the atom "foo" and cdr NIL would be represented by the i "1foo\0" and "#1#0\0".

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
