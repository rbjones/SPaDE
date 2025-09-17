# ProofPower HOL Interface for SPaDE

This file contatins the details of the SML functions needed to scape a ProofPower HOL theory database for SPaDE.
It is a mix of informal description of the process and a list of the SML functions needed to implement it.

## An informal account of the process

The process of scraping a ProofPower HOL theory database into a SPaDE repository involves traversing the theory hierarchy, extracting the relevant components of each theory, and writing them into the SPaDE native repository format.

To scrape the entire theory hieratchy first find what theories are available using get_theory_names.
Sort the theory names into a sequence in which no theory name appears before any of its ancestors, then process the theories in that order.

The top level of a repo is a folder which is the list of versions of the repo, which are numerically ordered, all the theories in the HOL database will be put in that directory, which will therefore by a labelled list of theories.
The last node of that list will be created after every theory has been written to the repo.

Each theory in turn is written to the repo.
Whenever a structure is to be written to the repo, its components must first be written, and the location in the sequence is remembered for use in the CONS cell which will link that component into the whole.
This can be done using a stack of positions.

In addition, the location of each theory should be remembered (though in principle it could be found) and of the last CONS in the top level folder.
The first component of a theory in the SPaDE repo will always be a list of parent theories which determine the context from which the sequence of extensions which forms the theory is begun.
This list includes the numerical position of each theory and the a signed cryptographic hash of the theory which is taken from the theory).
There follows a list of extensions, and concluded by a signed hash of the theory signeed by the server which created it.
In a first prototype these signed hashes may be omitted.
Note that the order of these components in terms of their numerical position in the repo will be that in the description, but the components will be combined in a list using CONS cells in hte given order, at each step adding a head to the list, so the order of the list is opposite to the order in the description.

Each extension consists of the signature of set of new type constructors and term constants (which may be empty) and a constraint, which may be either a new axiom or a constraint on the values of the new names.
This repository structure gives only meanings, and is not intended for the storage of theorems, for which other structures may be appropriate.
So, unlike the more typical role of LCF proof tools, there is no evidence in this repository of whether the extensions are conservative.
It is the intension in the broader structure of SPaDE that theorems when proving are signed by some authority as being derivable in a particular context, and the signing of of the theorem along with a cryptographic has of the context is what gives confidence in its derivability and truth.

The details of converting for the repo the signature and constraint of an extension, follow a similar pattern.
There are some differences between the structure of terms between ProofPower (and other HOLs), and SPaDE.
Two features are extra in SPaDE, which are TERM relocations and TERM listerals.
The former will not be needed for transcription of HOL theories.
The latter may be used instead of the use in ProofPower HOL of literal constants.
A literal constant in ProofPower HOL has a value derived from its name not a definition.
Such constants can be scraped as literal terms, this will suffice for some prototyping, but will leave a semantic deficit, which would precvetn a full and faithfull replication of the HOL theories making use of them in SPaDE.
The workings of TERM literals in SPaDE is not yet fully worked out, and as this is done, the mapping may need to be changed.

## SML Functions For Accessing ProofPower HOL Theories

At present this is just a list of signatures providing multiple ways of extracting and disassembling a ProofPower HOL theory hierarchy.
Some words may follow.

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

It is not necessary to open a theory to extract its components, and some theories (the ancestors of "basif-hol") cannot be opened.

```sml
get_types : string -> TYPE list
get_type_arity : string -> int OPT
get_axioms : string -> (string list * THM) list
get_consts : string -> TERM list
get_defn : string -> string -> THM
get_defns : string -> (string list * THM) list
```

In the SPaDE repository, signatures of types and constants are coupled with their defining constraints more closely than in ProofPower HOL, and types and constants can be introduced in a single extension with a single constraint.
This will not be required in transcribing a HOL theory, but it is necessary to gather together for each HOL definition, the list of constants defined and the defining constraint.
The best way to do this is not yet clear.
The two possibilities which come to mind are:

1. Use the tags against which a definition is stored to identify the constants defined.
2. Analyse the constraints to determine in which constraints each constant first appears.

The first is simplest, and should suffice for a first prototype.
If it should prove fallible we will need to think again.

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
