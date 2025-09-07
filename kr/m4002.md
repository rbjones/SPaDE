# ProofPower HOL Database Export

This page concerns the export of theories from the ProofPower HOL theorem prover into SPaDE knowledge repositories.
It includes a description of the structure of a SPaDE repository, which is of course also relevant to the export of theory hierarchies from other sources of knowledge or data.

Export is only one way of accessing in SPaDE knowledge or data which is not native to SPaDE.

It is also possible in principle to provide software which provides a SPaDE compatible view of other data sources without exporting them to a SPaDE native repository, and it is likely that this will be done for some important sources of data.
To support that kind of access you need to know the view presented to applications of SPaDE repositories, which will typically be through appropriate SDKs for the programming languages involved.

If such a repository is to be used by the deductive kernel or deductive intelligence then it will need to be accessed by the kr component of SPaDE, and presented to the deductive parts together with any other sources relevant to the application.
That interface is not the subject of this document, and has not yet been defined.

## The Native SPaDE Repository Structure

## The ProofPower Interface for Exporting Theories

The functions described here are not intended for export of ProofPower theories, but are those which are part of the standard system and which can be used to extract the necessary information.

The name and type of the functions should be sufficient explanation for this purpose, the ProofPower reference manual may be consulted for further details.

- theory_names: unit -> string list

- get_ancestors: string -> string list

- get_parents: string -> string list

- get_children: string -> string list

- get_types: string -> TYPE list

- get_consts: string -> TERM list

- get_defns: string -> (string list * THM) list

- get_axioms: string -> (string list * THM) list

- get_thms: string -> (string list * THM) list

Functions for taking apart objects of type TYPE, TERM and THM will also be needed:

- dest_simple_type: TYPE -> DEST_SIMPLE_TYPE

- dest_simple_term: TERM -> DEST_SIMPLE_TERM

- dest_thm: THM -> SEQ

Of course, you need to know those types:

```sml
datatype DEST SIMPLE TYPE=
Vartype of string
| Ctype of (string ∗ TYPE list);

datatype DEST SIMPLE TERM=
Var of string ∗ TYPE
| Const of string ∗ TYPE
| App of TERM ∗ TERM
| Simpleλ of TERM ∗ TERM ;

type SEQ = (TERM list) ∗ TERM ;
```
