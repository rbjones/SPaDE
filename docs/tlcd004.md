# The Theory of T-expressions

## Introduction

The purpose of this document is to formally define in ProofPower HOL the theory `T_ex`, a type of T-expressions which will be fundamental to the SPaDE system.
It responds to the requirement raised by task description [tltd004.md](tltd004.md) (to which reference should be made for any details of the task which do not belong here, particlarly refernce to documentation for ProofPower HOL, the language in which the specifications are to be written), providing in the early drafts the more detailed technical description necessary for the formalization of T-expressions in ProofPower HOL.

The task will be complete when the details are fully captured in formal text (HOL in sml) which is processed by ProofPower in the SPaDE build sequence and creates the required T_ex theory, upon which the entire SPaDE architecture rests.

Some proofs are necessary for the introduction of the new type, its associated operations.
Their basic properties, including an induction principle for T-expressions are to be proven.

T-expressions are a free algebra or inductive datatype.
In order to introduce the type we must choose a representation set and define operators over that set which together provide a structure isomorphic to the desired type T_ex and its primitive operations.
In order to implement T-expressions for SPaDE in Python or to represent them across an MCP interface as JSON, we also need a representation, and it is natural to choose one closely related to the representation set used in the formal definition.

The T_ex type itself is *architectural*, but the manner of concrete representation (for storage or presentation) is not, and may vary across different implementations.
For example, all forms of data storage can be interpreted as SPaDE repositories, given a kr variant designed for that storage idiom.
Though rooted in just one primitive foundational representation, SPaDE is intended to be multilingual by semantic embedding, so that many different concrete syntaxes may be used in presenting the expressions. 

The representation type we choose is that of byte sequences, (which we will denote by the type abbreviation  BS, an abbreviation for the HOL type CHAR LIST), and the set of representatives will be the closure of the empty set of byte sequences under a single T-expressions constructor.

The specification is to be undertaken in the following stages:
1. [Type Aliases](#type-aliases) aligning ProofPower types with SPaDE vocabulary.
2. [Packing and Unpacking](#packing-and-unpacking) of byte sequences.
3. [Representing T-expressions](#representing-t-expressions) as byte sequences, by defining the constructor and destructor over byte sequences, and obtaining the set of representatives as closure of the empty set under the constructor.
4. [The Type T_ex](#the-type-t_ex) Abstracting from the byte sequence representation to an isomorphic structure over the new type T_ex.
5. [Induction over T-expressions](#induction-over-t-expressions) Proving that the constructor (mk_T_ex) is OneOne, that the destructor (dest_T_ex) is a left inverse of the constructor and that the type T_ex satisfies the induction principle.

```sml
new_SPaDE_theory ("T_ex", "SPaDEroot", []);
```

## Type Aliases

SPaDE (and the version of ProofPower we are working with) are not tied to single byte representations of characters.
The utf8 branch of ProofPower uses the utf8 encoding for characters, which may occupy more than one byte.
SPaDE is intended to be agnostic as to the represenation of characters, and allows byte sequences for names and data of any format.
This may cause some awkwardness for the JSON representation used in the MCP interface, but these will only affect the presentation of names which are not valid UTF-8 sequences, which are unlikely in the terran diasporan repository.

We therefore prefer to think of the type CHAR as a single byte and STRING as a sequence of bytes.
For concision, we will use the abbreviations B and BS.

In order to represent structured entities in SPaDE, we make use of an algorithm to pack multiple byte sequences into a single byte sequence.
This is done by using a zero byte (null) to mark the end of each constituent byte sequence.
Since the sequences might contain zero bytes themselves, an escape byte (1) is used to indicate that the following byte should be interpreted literally rather than as a terminator.

When a string is converted to be suitable for concatenation in that way, with a null terminator added and escape characters inserted as needed, we call it a null-terminated byte string and use the acronym NTBS (though this will not be a HOL type).
When several such NTBS are concatenated together we may use the acronym NTBSS for the result.
An NTBSS is not a NTBS, but the packing algorithm can be applied to convert it into an NTBS.
NTBS and NTBSS are kinds of byte sequences which are not coextensive with the type BS, but the collection obtained by starting from the empty set and repeating a construction which yields an NTBSS will be used as representation for the type T_ex (short for T-expression) which this document defines. 

Here are the type aliases for B and BS:

```sml
declare_type_abbrev ("B", [], ⌜:CHAR⌝);
declare_type_abbrev ("BS", [], ⌜:CHAR LIST⌝);
```

## Packing and Unpacking

The algorithms for and unpacking algorithms for null-terminated byte sequences have the following types.

```sml
ⓈHOLCONST
│   mk_NTBS : BS → BS;
│   dest_NTBS : BS → BS × BS
├──────
│   T
■
```

The algorithms for packing and unpacking are as follows.

On packing, every byte `0` is written as the two bytes `1 0`. A byte `1` that precedes `0`, precedes `1`, or is the last byte of the input, is written as the two bytes `1 1`. A byte `1` that precedes any other byte is copied unchanged. Every other byte is copied. The byte `0` is then written at the end.

On unpacking, bytes are read until an unescaped `0`. An escape that precedes `0` contributes a `0`. An escape that precedes `1` contributes a `1`. An escape that precedes any other byte contributes both bytes. The terminating `0` is discarded. The bytes after it are the remainder.

The same cases, written as the bytes of the encoded content and then the terminating `0`:

| Input bytes | Encoded bytes, including the terminator |
| --- | --- |
| (empty) | `0` |
| `hello` | `hello` `0` |
| `0` | `1 0` `0` |
| `1` | `1 1` `0` |
| `0 1` | `1 0` `1 1` `0` |
| `1 2` | `1 2` `0` |
| `1 0` | `1 1` `1 0` `0` |
| `1 1` | `1 1` `1 1` `0` |
| `a 0 b 1 c` | `a` `1 0` `b` `1` `c` `0` |

An NTBSS is the concatenation of zero or more NTBS.

The following functions pack a list of byte sequences into a single byte sequence by first converting each to null terminated form and then concatenating them.
This is what we are calling an NTBSS.
It is not an NTBS.

The following function takes a list of byte sequences and packs them into an NTBSS.

```sml
ⓈHOLCONST
│   mk_NTBSS : BS LIST → BS
├──────
│       mk_NTBSS [] = []
│ ∧ ∀(s:BS) (ss:BS LIST)⦁
│       mk_NTBSS (Cons s ss) = (mk_NTBS s) @ (mk_NTBSS ss)
■
```

The following definition is not proven consistent automatically and a consistency proof will be necessary before it can be used in proofs.

```sml
new_conjecture(["dest_NTBS_consistent"],
    ⌜∃(dest_NTBSS:BS→(BS LIST))⦁
    ∀(bs:BS)⦁ dest_NTBSS bs =
       let (fstbs, rest) = dest_NTBS bs
       in  Cons fstbs (dest_NTBSS rest)⌝);
```

```sml
ⓈHOLCONST
│   dest_NTBSS : BS → BS LIST
├──────
│   ∀bs:BS⦁ dest_NTBSS bs =
│       let (fstbs, rest) = dest_NTBS bs
│       in  Cons fstbs (dest_NTBSS rest)
■
```

## Representing T-expressions

T-expressions will be represented (before type abstraction) as byte strings, but only those byte strings which can be reached by repeated application of the T-expression constructor.
That they are reachable in this way is essential to the principle of induction without which proving general properties about T-expressions would not be possible.
The construction always yields an NTBSS, and therefore any byte sequence which does not end in an unescaped null cannot be the representation of a T-expression.

A T-expression may be thought of as a constructor in an abstract syntax, or more generally as an element in an inductively defined set or free algebra.
The construction takes a single byte sequence which might be the name of the constructor in the abstract syntax, and a finite list of T-expressions which would then be represent the constituents of the constructed expression.
The former is simply a byte sequence and the latter is a finite sequence of byte sequences representing T-expressions.
The constructor adds the first argument to the front of the sequence (head of the list), and then converts the whole into an NTBSS.

Only the first argument is an arbitrary byte sequence; the second must be a finite list of TEXRs.

The types of the constructor and destructor over the representation type might be written as, showing the distinction between the first parameter which is an arbitrary byte sequence and the second which is a finite list of T_ex representations (which are byte sequences, but only those which are reachable by repeated application of the T-expression constructor).

```sml
ⓈHOLCONST
│mk_T_ex_rep : BS × BS LIST → BS;
│    dest_T_ex_rep : BS → BS × BS LIST
├──────
│   T
■
```

However, this is just a minor adjustment to the signature of mk_NTBSS and dest_NTBSS.
The extra constraints on the arguments can be stipulated when forming the closure operation which defines the set of T_ex representations.
So there is no need to define those functions.

The closure condition is then that a set of byte sequences is mk-T-ex-rep-closed if, whenever it contains all the elements of a finite list of T_ex representations, it also contains the result of applying mk_T_ex_rep to an arbitrary byte sequence and that list, which is to say applying mk_NTBSS to the concatenation of the byte sequence and the list of T_ex representations.
(All T_ex representations are NTBSS, not NTBS, the mk_T_ex_rep constructor converts each element of the list into NTBS in order to pack them into an NTBSS.)

The closure of the empty set under the mk_T_ex_rep constructor yields the set of all T_ex representations.
This set is used to introduce the type T_ex.

## The Type T_ex

To introduce the type T_ex, the theorem that the closure of the empty set under the mk_T_ex_rep constructor is non-empty is required.
This is straightforward as any byte sequence together with an empty list of T_ex representations is in the closure, ensuring non-emptiness.

Once the type is introduced the constructor and destructor over the representation type can be lifted to the new type, providing the functions mk_T_ex and dest_T_ex.

```sml
new_type ("T_ex", 0);
```

The types of the constructor and destructor are to be as follows:

```sml
ⓈHOLCONST
│   mk_T_ex : BS × T_ex LIST → T_ex;
│   dest_T_ex : T_ex → BS × T_ex LIST
├──────
│   T
■
```

The type T_ex is the closure of the empty set under the constructor mk_T_ex (the first parameter being a byte sequence, and hence not required to be in the set, and the second a finite list of elements from the set).
The set of byte sequences with an empty list of T-expressions seed the iteration.
The set of representatives is then the closure of the empty set under the construction, which is the intersection of all sets closed under the construction.
The set of all byte sequences is thus closed, and therefore ensures that the closure exists and is a subset of that set (the type BS).

The new type can therefore be introduced as the intersection of the closed sets, together with the proof of non-emptiness.
The previously defined constructor and destructor over the representatives can then be lifted to the new type, and the required properties proved using the results on the representation type.

This time we prove a more regular statement of the left inverse:

```sml
new_conjecture (["dest_T_ex_left_inverse"],
    ⌜∀ sxs:BS × T_ex LIST⦁ dest_T_ex (mk_T_ex sxs) = sxs ⌝);
```

## Induction and Recursion over T-expressions

The type T_ex is to be the free algebra generated by the constructor mk_T_ex from the empty set of T-expressions.
It is therefore required to satisfy the following induction principle, which must be proven:

ⓈHOLCONST
│   ForAllL: 'a LIST → ('a → BOOL) → BOOL
├──────
│   ∀p⦁ ForAllL [] p = T
│   ∧   ForAllL (x::xs) p = (p x ∧ ForAllL p xs)
■

```sml
new_conjecture (["T_ex_induction_thm"], ⌜
    ∀P:T_ex → BOOL⦁
        (∀(s:STRING) (xs:T_ex LIST)⦁
            (∀x:T_ex⦁ ForAllL xs P)
            ⇒ P (mk_T_ex (s, xs)))
        ⇒ ∀ t⦁ P t⌝);
```
new_conjecture = (["T_ex_prim_rec_thm"], ⌜
    ⊢ ∀ f1 f2⦁ ∃⋎1 f⦁ ∀bs bss⦁
        f (mk_T_ex bs bss) = f1 bs (map f1 
    ∧   f (mk_T_ex bs bss) = f2 bs (map f2 bss))

## The Representation of the Free Algebra

The range of `pack_list` is in bijection with `STRING LIST`. It is not in bijection with the free algebra. A list of arbitrary byte sequences includes lists whose elements are not themselves representations of T-expressions.

The representation of `mk_T_ex (s, ts)` is `pack_list` applied to the label `s` followed by the representations of the elements of `ts`. The set of representations is the inductive subset of `STRING` generated from that clause. It is non-empty: the representation of `mk_T_ex ([], [])` is `pack_bytes []`, the one-byte string whose only byte is `0`.

The type `T_ex` is introduced as that subset. `mk_T_ex` and `dest_T_ex` are the constructor and its inverse on the new type. The existence of the subset, and the proof that the constructor is a bijection onto it, are the part of this theory that goes beyond the packing functions already coded in `kr/`.

The consistency mechanism in [tlcd002.md](tlcd002.md) is available when a specification paragraph states one of these properties and the automatic prover does not discharge it. The witness is defined first, the existence theorem is saved with `save_cs_∃_thm`, and the result will then be picked up in proof contexts which include 'savedthm_cs_∃_proof' including the SPaDEroot proof context.

## Historical Note

The key algorithms here were described and implemented in the kr subsystem to implement the S-expressions on which the first MCP prototype was based.
Some of this material can be brought forward for use in a new prototype based on T-expressions, which is likely to remain the foundational data structure for SPaDE.

It is the coding implemented by `encode_bytes` and the corresponding decode in [../kr/krcd009.py](../kr/krcd009.py), and exercised by [../kr/krte003.py](../kr/krte003.py).

## Outstanding Proofs

```sml
get_unproved_conjectures "-";
```

## Proformas

```
ⓈHOLCONST
│   
├──────
│   T
■
```
