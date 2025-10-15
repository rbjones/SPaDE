# ProofPower HOL Interface for SPaDE

This file contains the details of the SML functions needed to scrape a ProofPower HOL theory database for SPaDE.
It is a mix of informal description of the process and a list of the SML functions needed to implement it.

## An informal account of the process

The process of scraping a ProofPower HOL theory database into a SPaDE repository involves traversing the theory hierarchy, extracting the relevant components of each theory, and writing them into a SPaDE native repository in a different format.

The HOL theory hierarchy is accessed by invoking PolyML on the ProofPower HOL polyml database which contains the theories, loading the SML files containing the functions for exporting to the SPaDE native repository, and then invoking the top level function to scrape the theories.
Note that the various functions mentioned in this document for accessing the ProofPower HOL database are part of the standard ProofPower HOL system, and will therefore already be in place when PolyML is invoked on a ProofPower HOL database.

To scrape the entire theory hierarchy, first find what theories are available (using the sml procedure get\_theory\_names).
Sort the theory names into a sequence in which no theory name appears before any of its ancestors, (this can be checked using the sml procedure get\_parents or get\_ancestors) then process the theories in that order.

The top level of a SPaDE repo is a folder which is the list of versions of the repo, in which the constituent folder names are an initial segment of the natural numbers starting with 1.
All the theories in the HOL database will be put in folder "1" which will be the sole constituent of the top level folder, indicating that it is the first and only version of the repo.

Folders are lists of name/value pairs, where the value is either a theory or another folder.
That value is presented as a pair in which the first component is a tag indicating whether it is a folder or a theory, and the second component is the value.

Each theory in turn is written to the repository followed by the
structures which include it as a theory at the head of the folder (which is a list).
When all the theories have been written, a further folder is written to the repository, which is the top level folder of the repository, containing the single folder named "1" which contains all the theories.

Whenever a structure is to be written to the repo, its components must first be written, and their locations in the sequence are remembered for use in CONS cells which will link the components into the whole.
This can be done using a stack of positions, which are byte displacements in the binary file into which the repository is being written.

The first component of a theory in the SPaDE repo will always be a list of parent theories which determine the context from which the sequence of extensions which forms the theory is begun.
This list includes the path within the repository to the theory (including the repo version number), the byte displacement in the repo of each theory (i.e. a pointer to the theory) and a signed cryptographic hash of the theory which is taken from the theory).
There follows a list of extensions, and concluded by a signed hash of the theory signeed by the server which created it.
In a first prototype these signed hashes may be omitted.
Note that the order of these components in terms of their numerical position in the repo will be that in the description, but the components will be combined in a list using CONS cells in the given order, at each step adding a head to the list, so the order of the list is opposite to the order in the description.

Each extension consists of the signature of set of new type constructors and term constants (which may be empty) and a constraint, which is a closed term of type BOOL (and may or may not be conservative).
This repository structure gives only meanings, and is not intended for the storage of theorems, for which other structures may be appropriate.
So, unlike the more typical role of LCF proof tools, there is no evidence in this repository of whether the extensions are conservative.
It is the intention in the broader structure of SPaDE that alleged theorems are signed by some authority as being derivable in a particular context, and the signing of of the theorem along with a cryptographic hash of the context is what gives confidence in its derivability and truth (the level of confidence depending on the signing authority).

The details of converting for the repo the signature and constraint of an extension, follow a similar pattern.
There are some differences between the structure of terms between ProofPower (and other HOLs), and SPaDE.
Two features are extra in SPaDE, which are TERM relocations and TERM literals.
The former will not be needed for transcription of HOL theories.
The latter may be used instead of the use in ProofPower HOL of literal constants.
A literal in ProofPower HOL is a constant that has a value derived from its name not from a definition.
Such constants can be scraped as literal terms, this will suffice for some prototyping, but will leave a semantic deficit, which would prevent a full and faithful replication of the HOL theories making use of them in SPaDE.
The workings of TERM literals in SPaDE is not yet fully worked out, and as this is done, the mapping may need to be changed.

## SML Functions For Accessing ProofPower HOL Theories

At present this is just a list of signatures providing multiple ways of extracting and disassembling a ProofPower HOL theory hierarchy.
Some words may follow.

Note that these are functions already implemented in ProofPower HOL, and are not part of the SPaDE code base.
They are fully documented in the ProofPower HOL manual (usr029.pdf), this extract is for convenience of reference since that manual is large.

Probably not needed:

```sml
get_theory : string -> THEORY
get_theory_info : string -> THEORY_INFO
```

### Establishing the theory processing order

The following functions should suffice to establish what theories are available, and to determine the order in which they should be processed:

```sml
get_theory_names : unit -> string list
get_ancestors : string -> string list
get_parents : string -> string list
```

Probably not needed

```sml
get_children : string -> string list
```

### Extracting the components of a theory

It is not necessary to open a theory to extract its components, and some theories (the ancestors of "basic-hol") cannot be opened.

```sml
get_types : string -> TYPE list
get_type_arity : string -> int OPT
get_axiom : string -> string -> THM
get_axioms : string -> (string list * THM) list
get_consts : string -> TERM list
get_defn : string -> string -> THM
get_defns : string -> (string list * THM) list
get_thm : string -> string -> THM
get_thms : string -> (string list * THM) list
```

In the SPaDE repository, signatures of types and constants are coupled with their defining constraints more closely than in ProofPower HOL, and types and constants can be introduced in a single extension with a single constraint.
This will not be required in transcribing a HOL theory, but it is necessary to gather together for each HOL definition, the list of constants defined and the defining constraint.
The best way to do this is not yet clear.
The two possibilities which come to mind are:

1. Use the tags against which a definition is stored to identify the constants defined.
2. Analyse the constraints to determine in which constraints each constant first appears.

The first is probably simplest, and should suffice for a first prototype.
If it should prove fallible we will need to think again.

The extensions which form a theory can be established in the following way:

1. Gather the list of all definitions in the theory using get_defns. This list is in the reverse of the order in which the definitions were made. Each definition is a pair of a list of tags and a theorem. The tags are the names of the new constants or type constructorsintroduced, and the name of the definition (which is the last in the list and should be ignored for present purposes).
To establish the signature from this list it is necessary to establish whether each tag is a type or a constant.
This can be done using get_type_arity, which returns NIL if the name is not a type constructor, and Value n if it is a type constructor of arity n.
If it is not a type constructor, it must be a constant, and its type can be found using get_consts, which returns the list of all constants in the theory, from which the type of the constant can be found by matching names.

2. Retrieve the axioms using get_axioms.
Each axiom will form an extension with no new types or constants.  The order is not important in SPaDE, though it is in ProofPower HOL.

### Disassembling Theorems, Terms and Types

```sml
dest_thm : THM -> SEQ
asms : THM -> TERM list
concl : THM -> TERM

dest_simple_term: TERM -> DEST_SIMPLE_TERM

datatype DEST SIMPLE TERM=
Var of string ∗ TYPE
| Const of string ∗ TYPE
| App of TERM ∗ TERM
| Simpleλ of TERM ∗ TERM ;

dest_simple_type : TYPE -> DEST_SIMPLE_TYPE

datatype DEST SIMPLE TYPE=
Vartype of string
| Ctype of (string ∗ TYPE list);

is_vartype :  TYPE -> bool
is_ctype :  TYPE -> bool

is_var : TERM−> bool
is_const : TERM−> bool
is_app : TERM−> bool
is_λ : TERM−> bool

dest_vartype : TYPE -> string
dest_ctype : TYPE−> string ∗ TYPE list

dest_var: TERM−> (string ∗ TYPE)
dest_const: TERM−> (string ∗ TYPE)
dest_app: TERM−> (TERM ∗ TERM)
dest_λ: TERM−> (TERM ∗ TERM)
```

## Writing to a SPaDE Native Repository

Details of the structure a SPaDE native repository are given in [The SPaDE Native Repository](krdd002.md).

Writing to such a repository from ProofPower HOL to a large extent reflect the structure of the above functions for extracting the components of a ProofPower HOL theory.

The top level functions for scraping ProofPower HOL theories into a SPaDE native repository are:

```sml
(* Given the file name for a new SPaDE repository and a list of theory names, scrape those theories and their ancestry into the repository.)

scrape_pp_theories : string -> string list -> unit

(* Given the file name for a new SPaDE repository, scrape all the theories in the current ProofPower HOL database into the repository. *)

scrape_pp_db : string -> unit
```

The top level of a repository scraped from ProofPower HOL will be a folder of versions of the repo which contains version 1 only.
Version 1 of the repository will be a folder containing all the theories in the database.

A folder is a list of theories or folders.

In all cases the theories will be processed in an order in which no theory appears before any of its ancestors.

These top level functions will open a binary output stream to the given file name, will write a NIL at the beginning of the repository, and then write each theory to the repository as successive versions of a folder of theories.
 list of theories constructed using the repository coding of a CONS constructor.
It will then terminate the list will a CONS to NIL and create a top-level folder with the and will write the top level folder of the repository at the end of the process.

### Structural Differences between ProofPower HOL and SPaDE repositories

The differences between the structure of a ProofPower HOL theory and a SPaDE theory are not confined to the lower level represetation for storage in persistent media.

There are someimportant differences which arise from strategic decisions made in the design of SPaDE.
The most important of these are:

1. **Relative Names in SPaDE** HOL theory hierarchies are local to a single polyml database, whereas SPaDE repositories are intended to be global and long-lived.
This leads to a more complex naming structure for theories in SPaDE, into which the simple almost flat namespace of HOL theories must be mapped.

Note also, that the open-ended distributed nature of SPaDE repositories means that distinct repositories may be combined by adding an extra folder above two existing repositories (this will usually be the combining of two diasporic repositories into an extended diaspora).
To allow for this to be possible, the names used in SPaDE HOL terms are relative.

In a ProofPower HOL repository, though distributed across the theories in the ancestry of a theory, the names of types and constants in scope in that theory must be unique and are therefore simple names.

In SPaDE, the names of types and constants in the ancestors of a theory must be qualified by the path within the repository to the theory in which they are defined.
This can be achieved by including all the HOL theories in a single folder which constitutes one version of the SPaDE repository.
To refer in one theory to a name defined in another theory, the path to that theory must be included in the name, which if the hierarchy is imported from ProofPower HOL will require a one directory uplift and then a path through the theory name to the local name.
Thus, to refer in the theory *basic_hol* to the constant *name* in the theory "misc" the SPaDE name would be "(1,[misc;name])" (a pair consisting of a numeric uplift and a sequence of simple names).

2. **Translation of ProofPowerLiterals** The structure of a SPaDE HOL term is more complex than that of a ProofPower HOL term, since it includes term relocations and TERM literals.

Term relocations will never be present in a SPaDE repository, they are only there to mediate in use of terms outside the context in which they were constructed, so they will not be needed in transcribing HOL theories.

Literal terms in ProofPower are a special class of constants which have a meaning derived from their name rather than from a definition.
In SPaDE, literals are a more general mechanism, and the mapping from ProofPower HOL to SPaDE will be to use TERM literals in SPaDE to represent HOL literal constants.
However, to do this the syntactic rules governing which constants are literal constants must be known.

However, an expedient may be adopted which will suffice for prototyping, which is underpinned by the fact that no ProofPower HOL theory will contain constants which have not been defined, except for the literal constants.
So any constant in a theory which is not defined in that theory or any of its ancestors must be a literal constant, and can be transcribed as a TERM literal in SPaDE.

The effect of these requirements is that the transcription program must know when transcribing a theory, the theory in which each name in scope was defined, so that the correct relative name can be constructed, and any literal constants can be identified.

Theorems in SPaDE are digitally signed sequents, and this applies also to the constraints associated with the introduction of new constants in a theory, and even to axiomatic constraints which introduce no new names.

In the former case the signature gives a degree of confidence that the extension is conservative, in the latter that it is consistent with the prior theory.
There are therefore three kinds of theorem in the SPaDE system corresponding to conservative extensions, consistent axiomatic extensions and derived theorems.

For the sake of prototyping, the digital signatures may be omitted, but the structure must be in place to allow them to be added later.

### Writing a SPaDE repository

When scraping a ProofPower HOL theory database, the resulting SPaDE repository will have only one version, which will be version "1".
So the top level of the repository will be a folder containing a single folder named "1" which contains all the theories in the database.
Folders are created incrementally by writing each constituent theory or folder followed by a CONS cell linking it to the rest of the folder, which is terminated by a NIL.
This is slightly complicated by folders not being mere lists of theories, but lists of pairs of names and theories or folders.

In order to incrementally write this folder it is of course necessary to record the byte displacement in the file of each prior part of folder, as well as the start of the next theory.
Once the theory is complete, its name is written and consed with the theory and the pair is then connected at the head of the folder to the previous part of the folder.

This kind of maneuvre is needed at all levels of the repository, since all structures are built up from their components using CONS cells.
A stack could be used to manage the process, but the implicit stack associated with functional recursion might suffice.

### Writing a theory to the repository

The first step in writing a theory to the repository is to establish the context in which the theory is to be understood.

This is done by identifying one or more parents, the ancestry of which will determine the context (and hence the namespace) in which the theory is defined.
In order to ensure reliable preservation of the context in which any theorem has been derived, digital signatures are used, so this first part of a theory in which the context is recorded is not merely a set of parent names.
It includes cryptographic hashes of the parent theories, and a digital signature of the whole context by the authority which created the theory.

In the first instance, for prototyping, these signatures may be omitted, but the structure must be in place to allow them to be added later.
In SPaDE parents need not be in the same local repository, but may be remote.
In either case not only the path to the parent theory, but also the displacement in its own local repository are included in the context structure and in a terminating hash created from the whole theory.

The context structure is followed by a list of extensions, each of which introduces new names (possibly none) and a constraint (which may be an axiom or a conservative extension).

