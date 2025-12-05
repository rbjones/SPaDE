(* HOL4 specification of SPaDE repository 

Preliminaries 

This document is in SML, augmented by the facilities provided by HOL4.
In this document those augmentations primarily concern the definition
of types and terms in HOL.

First we have to establish a HOL4 context in which the definitions
can be processed.
*)

app load ["bossLib", "stringTheory"];
open bossLib Theory Parse;
local open stringTheory pred_setTheory in end;
val _ = new_theory "SPaDE_KR_Spec";

(* S-expressions

Underlying the HOL structures in SPaDE native repositories there is replica of the LISP S-expression structure, which is a simple binary tree structure in which each node is either an atom or a pair of nodes.

This is mentioned here not because of its role in the representation of terms in the repository, but because it is used here for the structure of literal terms, which are explicit constants whose value is given by their structure as an S-expression.
 *)

Datatype: sexp =
      Atom string
    | Nil
    | Cons sexp sexp
End

(* Names

Names are relative giving a place in the heirarchic structure relative to some given place.
They are therefore represented as a number indicating a height above the current folder, and a path downward from that folder.
Each stage selects a new folder, the last of which will be a theory.

Note that "string" here should be read as an arbitrary byte sequence, since names may contain characters outside the normal unicode range.
This might not properly correspond to HOL strings in HOL4, but is necessary to support the full range of possible names.
*)

val _ = Datatype `sname = Sn string`;
val _ = Datatype `rname = Rn num (sname list)`;


(* Hashes

A signed cryptographic hash is a byte sequence, represented as a string (i.e. an arbitrary byte sequence).
*)

val _ = Datatype `shash = Sh string`;

(* Types *)

val _ = Datatype
        `htype = Tyv sname
               | Tyc rname (htype list)`;

(* Terms

Because names are relative, comparing constants in terms is complicated by the possibility of using constants in distinct contexts, and the need to adjust to a common context.
There are several ways to approach this difficulty, and a final decision may not be made until prototyping is well progressed.
Meanwhile provision is made in this specification for terms to be relocated.

In the following we have the normal four kinds of term, variables, constants, applications and abstractions, with the addition of a term relocator.
*)

val _ = Datatype
      `hterm = Tmv sname
             | Tmc rname htype
             | Tapp hterm hterm
             | Tabs sname htype hterm
             | Tloc rname hterm
             | Tlit sexp;             

(* Sequents *)

val _ = Datatype
      `hsequent = Sg (hterm list) hterm`;

(* Signature *)

Datatype: hsig =
      <| types: (rname # num)list;
         constants: (rname # htype)list
      |>
End

(* Extension *)

Datatype: hext =
      <| signature: hsig;
         constraint: hterm
      |>
End

(* Theory *)

Datatype: htheory =
      <| thname: sname;
         parents: rname list # shash;
         extensions: hext list;
         shash: shash
      |>
End

(* Folders

Folders are used to structure the repository hierarchically, and contain theories or other folders.
*)

val _ = Datatype `folder = Rdict (((num + sname) # 'b) list)`;

(* Trees

I was looking for a much tighter charactersation of versioned trees, but this involved recursions in Datatype constructions which are not supported.
So this is a simpler tree datatype which will suffice.
*)

val _ = Datatype
 `rtree =
   Rfolder (rtree rdict)   |
   Rleaf 'a`;

(* The Repository *)

val _ = Datatype `hrepo = Hrepo (htheory rtree)`;
