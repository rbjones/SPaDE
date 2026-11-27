# The Theory of T-expressions

## Introduction

The purpose of this document is to formally define in ProofPower HOL the theory `T_ex`, a type of T-expressions which will be fundamental to the SPaDE system.
It responds to the requirement raised by task description [tltd004.md](tltd004.md) (to which reference should be made for any details of the task which do not belong here, particlarly refernce to documentation for ProofPower HOL, the language in which the specifications are to be written), providing in the early drafts the more detailed technical description necessary for the formalization of T-expressions in ProofPower HOL.

The task will be complete when the details are fully captured in formal text (HOL in sml) which is processed by ProofPower in the SPaDE build sequence and creates the required T_ex theory, upon which the entire SPaDE architecture rests.

Some proofs are necessary for the introduction of the new type, its associated operations.
Their basic properties, including an induction principle for T-expressions and a recursion principle for recursively defining functions over T-expressions, are to be proven.

T-expressions are a free algebra or inductive datatype.
In order to introduce the type we must choose a representation set and define operators over that set which together provide a structure isomorphic to the desired type T_ex and its primitive operations.
In order to implement T-expressions for SPaDE in Python or to represent them across an MCP interface as JSON, we also need a representation, and it is natural to choose one closely related to the representation set used in the formal definition.

The T_ex type itself is *architectural*, but the manner of concrete representation (for storage or presentation) is not, and may vary across different implementations.
For example, all forms of data storage can be interpreted as SPaDE repositories, given a kr variant designed for that storage idiom.
Though rooted in just one primitive foundational representation, SPaDE is intended to be multilingual by semantic embedding, so that many different concrete syntaxes may be used in presenting the expressions. 

The representation type we choose is that of byte sequences, (which we will denote by the type abbreviation  BS, an abbreviation for the HOL type CHAR LIST, which is really byte LIST), and the set of representatives will be the closure of the empty set of byte sequences under a single T-expressions constructor.

The specification is to be undertaken in the following stages:
1. [Type Aliases](#type-aliases) aligning ProofPower types with SPaDE vocabulary.
2. [Packing and Unpacking](#packing-and-unpacking) of byte sequences.
3. [Representing T-expressions](#representing-t-expressions) as byte sequences, by defining the constructor and destructor over byte sequences, and obtaining the set of representatives as closure of the empty set under the constructor.
4. [The Type T_ex](#the-type-t_ex) Abstracting from the byte sequence representation to an isomorphic structure over the new type T_ex.
5. [Induction and Recursion over T-expressions](#induction-and-recursion-over-t-expressions) Proving that the constructor (mk_T_ex) is OneOne, that the destructor (dest_T_ex) is a left inverse of the constructor and that the type T_ex satisfies the induction principle.

```sml
new_SPaDE_theory ("T_ex", "SPaDEroot", []);
set_pc "SPaDEroot";
```

## Miscellanea

These probably all belong elsewhere, but remain here pro-tem.

### List Processing

The following function takes a list of byte sequences and packs them into an NTBSS.

```sml
ⓈHOLCONST
│   Flatten : 'a LIST LIST → 'a LIST
├──────
│           Flatten [] = []
│ ∧ ∀e l⦁   Flatten (Cons e l) = e @ (Flatten l)
■
```

The following function is intended to make recursive processing of lists more transparent by separating out the recursion involved in processing the list from the functionality being applied to each element.
It takes a state machine and turns it into a function over lists.

```sml
ⓈHOLCONST
│   Iterate1 : ('i OPT × 's → 's × 'o LIST) → ('i LIST × 's) → ('s × 'o LIST)
├──────
│   ∀ (sm:'i OPT × 's → 's × 'o LIST) (ins:'s) (fi: 'i) (il: 'i LIST) ⦁
│       Iterate1 sm ([], ins) = sm (Undefined, ins)
│ ∧     Iterate1 sm ((Cons fi il), ins) =
│            let (ns, nol) = sm (Value fi, ins)
│            in  let (fs, to) = Iterate1 sm (il, ns)
│                in  (fs, nol @ to)
■
```

A property of a function defined by `Iterate1` is proved by induction on the input list. The property may mention the state and the result. On the empty list, `Iterate1` applies the state machine to `Undefined`. In the step, the state machine is applied to `Value` of the head, and the inductive hypothesis is the result of `Iterate1` on the tail, started from the state which that application returns.

```sml
new_conjecture (["Iterate1_induction_thm"], ⌜
    ∀ (sm:'i OPT × 's → 's × 'o LIST)
      (P:'i LIST → 's → 's × 'o LIST → BOOL) ⦁
        (∀ (ins:'s) ⦁ P [] ins (sm (Undefined, ins)))
      ∧ (∀ (fi:'i) (il:'i LIST) (ins:'s) ⦁
            let (ns, nol) = sm (Value fi, ins)
            in  let (fs, to) = Iterate1 sm (il, ns)
                in  P il ns (fs, to)
                    ⇒ P (Cons fi il) ins (fs, nol @ to))
      ⇒ ∀ (il:'i LIST) (ins:'s) ⦁
            P il ins (Iterate1 sm (il, ins))⌝);
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
An NTBSS is not an NTBS, but the packing algorithm can be applied to convert it into an NTBS.
NTBS and NTBSS are kinds of byte sequences which are not coextensive with the type BS, but the collection obtained by starting from the empty set and repeating a construction which yields an NTBSS will be used as representation for the type T_ex (short for T-expression) which this document defines. 

Here are the type aliases for B and BS:

```sml
declare_type_abbrev ("B", [], ⌜:CHAR⌝);
declare_type_abbrev ("BS", [], ⌜:CHAR LIST⌝);
```

## Packing and Unpacking

We refer to the process of converting BS to null-terminated byte strings (NTBS) and concatenated null-terminated byte strings (NTBSS) as packing, and the reverse process as unpacking.
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

To formally define the conversion from BS to NTBS, we introduce the function `mk_NTBS_step` which handles one byte at a time, and `mk_NTBS` which iterates this step over the entire byte sequence.

```sml
ⓈHOLCONST
│   mk_NTBS_step : B OPT × BOOL → BOOL × BS
├──────
│   ∀(bopt:B OPT) (esc:BOOL) ⦁
│        mk_NTBS_step (bopt, esc) =
│           if esc
│           then    if ValueOf bopt = AbsChar 0 ∨ ValueOf bopt = AbsChar 1
│                   then (F, [AbsChar 1; AbsChar 1; ValueOf bopt])
│                   else (F, [ValueOf bopt])
│           else    if bopt = Value(AbsChar 1)
│                   then (T, [AbsChar 1])
│                   else (F, [ValueOf bopt])
■
```

```sml
ⓈHOLCONST
│   mk_NTBS : BS → BS
├──────
│   ∀bs⦁ mk_NTBS bs = Snd(Iterate1 mk_NTBS_step (bs, F))
■
```

The following function packs a list of byte sequences into a single byte sequence by first converting each to null terminated form and then concatenating them.
This is what we are calling an NTBSS.
It is not an NTBS (unless the list contains exactly one byte sequence).

```sml
ⓈHOLCONST
│   mk_NTBSS : BS LIST → BS
├──────
│       mk_NTBSS = Flatten o (Map mk_NTBS)
■
```

```sml
declare_alias ("B", ⌜mk_NTBS⌝);
```

```sml
new_conjecture (["mk_NTBS_not_empty_thm"],
    ⌜∀(bs:BS)⦁ ¬ mk_NTBS bs = []⌝);
```

```sml
set_goal([], ⌜∀(bs:BS)⦁ ¬ mk_NTBS bs = []⌝);
a (rewrite_tac [get_spec ⌜mk_NTBS⌝] THEN strip_tac);
a (strip_asm_tac (∀_elim ⌜bs⌝ list_cases_thm)
    THEN (asm_rewrite_tac ((map get_spec [⌜Iterate1⌝, ⌜mk_NTBS_step⌝])@[let_def])));
a (cases_tac ⌜x = AbsChar 1⌝ THEN asm_rewrite_tac[get_spec ⌜$@:BS LIST → BS LIST → BS LIST⌝]);
val mk_NTBS_not_empty_thm = save_pop_thm "mk_NTBS_not_empty_thm";
```

```sml
new_conjecture (["OneOne_mk_NTBSS_thm"],
    ⌜OneOne mk_NTBSS⌝);
```

```
stop;
set_goal([], ⌜OneOne mk_NTBSS⌝);
a (rewrite_tac(map get_spec [⌜OneOne⌝, ⌜mk_NTBSS⌝, ⌜mk_NTBS⌝, ⌜Flatten⌝]));
a (REPEAT ∀_tac);
a (lemma_tac ⌜⌝)
a (list_induction_tac ⌜x1⌝);
(* *** Goal "1" *** *)
a (rewrite_tac(map get_spec [⌜Map⌝, ⌜mk_NTBS⌝, ⌜mk_NTBS_a⌝, ⌜Flatten⌝]));
a (lemma_tac ⌜Map ⌝);
get_spec ⌜Map⌝;
```

Unpacking an NTBSS can be done using the `dest_NTBSS` function, which iteratively applies `dest_NTBSS_step` to extract each NTBS and any residual bytes.

```sml
ⓈHOLCONST
│   dest_NTBSS_step : B OPT × (BOOL × BS) → (BOOL × BS) × BS LIST
├──────
│   ∀(bopt:B OPT) (esc:BOOL) (pbs:BS)⦁
│   dest_NTBSS_step (bopt, (esc, pbs)) =
│   if bopt = Undefined
│   then ((esc, pbs), [])
│   else if esc
│   then    if ValueOf bopt = AbsChar 0 ∨ ValueOf bopt = AbsChar 1
│           then ((esc, pbs @ [ValueOf bopt]), [])
│           else ((esc, pbs @ [AbsChar 1; ValueOf bopt]), [])
│   else if ValueOf bopt = AbsChar 0
│   then ((F, []), [pbs])
│   else if ValueOf bopt = AbsChar 1
│   then ((T, pbs), [])
│   else ((F, pbs), [])
■
```

In the following unpack specification, which is intended to be applied to a concatenation of NTBS, the first component in the result is any residue which appears after the last NTBS in the byte sequence.
The residue is partly decoded and if it ends with an escape character that character will not be in the residual byte sequence, but will cause the accompanying BOOL to be T.

```sml
ⓈHOLCONST
│   dest_NTBSS : BS → (BOOL × BS) × BS LIST
├──────
│   ∀bs:BS⦁ dest_NTBSS bs = Iterate1 dest_NTBSS_step (bs, (F, []))
■
```

```sml
new_conjecture(["dest_mk_NTBSS_lemma"], ⌜∀bss:BS LIST⦁ dest_NTBSS (mk_NTBSS bss) = ((F, []) , bss)⌝);
```

```
set_goal([], ⌜∀bss:BS LIST⦁ dest_NTBSS (mk_NTBSS bss) = ((F, []) , bss)⌝);
a (strip_tac THEN rewrite_tac (map get_spec [⌜dest_NTBSS⌝, ⌜mk_NTBSS⌝, ⌜Iterate1⌝,⌜Flatten⌝]));
a (strip_asm_tac (∀_elim ⌜bss:BS LIST⌝ list_cases_thm)
    THEN TRY (asm_rewrite_tac (map get_spec [⌜dest_NTBSS⌝, ⌜dest_NTBSS_step⌝, ⌜mk_NTBSS⌝, ⌜Iterate1⌝,⌜Flatten⌝])));
stop;

```

## Representing T-expressions

T-expressions will be represented (before type abstraction) as byte strings, but only those byte strings which can be reached by repeated application of the T-expression constructor starting from the empty list of T-expressions.
That they are reachable in this way is essential to the principle of induction without which proving general properties about T-expressions would not be possible.
The construction always yields an NTBSS, and therefore any byte sequence which does not end in an unescaped null cannot be the representation of a T-expression.

A T-expression may be thought of as a constructor in an abstract syntax, or more generally as an element in an inductively defined set or free algebra.
The construction takes a single byte sequence which might be the name of the constructor in the abstract syntax, and a finite list of T-expressions which would then represent the constituents of the constructed expression.
The former is simply a byte sequence and the latter is a finite sequence of byte sequences representing T-expressions.
The constructor adds the first argument to the front of the sequence (head of the list), and then converts the whole into an NTBSS.

Only the first argument is an arbitrary byte sequence; the second must be a finite list of T_ex representations.

The types of the constructor and destructor over the representation type might be written as ⓣBS × BS LIST⌝, showing the distinction between the first parameter which is an arbitrary byte sequence and the second which is a finite list of T_ex representations (which are byte sequences, but only those which are reachable by repeated application of the T-expression constructor).

```sml
ⓈHOLCONST
│   mk_T_ex_rep : BS × BS LIST → BS;
│   dest_T_ex_rep : BS → BS × BS LIST
├──────
│   ∀(bs:BS) (bl:BS LIST)⦁
│       mk_T_ex_rep (bs, bl) = mk_NTBSS (Cons bs bl)
│∧      dest_T_ex_rep bs = let (_, bss) = dest_NTBSS (bs) in (Hd bss, Tl bss)
■
```


The second argument is required to be a finite list of T_ex representations. This requirement is captured by the definition of `is_T_ex_rep`, which checks membership in the intersection of all sets closed under the `mk_T_ex_rep` constructor.

We need to prove that a T_ex representation exists, that the set of T_ex representations is non-empty, in order to justify the introduction of the type T_ex.

The extra constraints on the arguments can be stipulated when forming the closure operation which defines the set of T_ex representations.

```sml
ⓈHOLCONST
│   is_T_ex_rep : BS → BOOL
├──────
│   ∀(bs:BS)⦁
│       is_T_ex_rep bs = bs ∈
│        ⋂{S | ∀e el⦁
│                    List2Set el ⊆ S
│                ⇒   mk_T_ex_rep (e, el) ∈ S}
■
```

The closure condition is then that a set of byte sequences is mk-T-ex-rep-closed if, whenever it contains all the elements of a finite list of T_ex representations, it also contains the result of applying mk_T_ex_rep to an arbitrary byte sequence and that list, which is to say applying mk_NTBSS to the concatenation of the byte sequence and the list of T_ex representations.
(All T_ex representations are NTBSS, not NTBS, the mk_T_ex_rep constructor converts each element of the list into NTBS in order to pack them into an NTBSS.)

```sml
set_goal([], ⌜∃s⦁ is_T_ex_rep s⌝);
a (rewrite_tac [get_spec ⌜is_T_ex_rep⌝]);
a (∃_tac ⌜mk_T_ex_rep ([],[])⌝
    THEN rewrite_tac (map get_spec [⌜$⋂⌝, ⌜$⊆⌝, ⌜$∈⋎L⌝, ⌜List2Set⌝])
    THEN REPEAT strip_tac);
a (list_spec_nth_asm_tac 1 [⌜[]:BS⌝,⌜[]:BS LIST⌝]);
val T_ex_rep_non_empty_thm = pop_thm();
```

```sml
set_goal([],⌜∀P:BS → BOOL⦁
        (∀(bs:BS) (bsl:BS LIST)⦁
            (∀e⦁ e ∈⋎L bsl ⇒ P e) ⇒ P (mk_T_ex_rep (bs, bsl)))
        ⇒ ∀(bs:BS)⦁ is_T_ex_rep bs ⇒ P bs⌝);
a (rewrite_tac (map get_spec [⌜is_T_ex_rep⌝, ⌜mk_T_ex_rep⌝]) THEN REPEAT strip_tac);
a (spec_nth_asm_tac 1 ⌜{bs | P bs}⌝);
a (list_spec_nth_asm_tac 4 [⌜e⌝, ⌜el⌝]);
a (swap_asm_concl_tac ⌜List2Set el ⊆ {bs|P bs}⌝);
a (rewrite_tac (map get_spec [⌜$⊆⌝,⌜$∈⋎L⌝,⌜List2Set⌝]));
a (REPEAT strip_tac);
a (∃_tac ⌜e'⌝ THEN REPEAT strip_tac);
val T_ex_rep_induction_thm = save_pop_thm("T_ex_rep_induction_thm");
```

```sml
new_conjecture (["T_ex_rep_prim_rec_thm"], ⌜
    ∀ f1 f2⦁ ∃⋎1 f⦁ ∀ bs bs2 bss1 bss2⦁
        f (mk_T_ex_rep (bs, [])) = f1 bs
    ∧   f (mk_T_ex_rep (bs, Cons bs2 bss2)) = f2 bs (map f (Cons bs2 bss2))⌝);
```

```sml
set_goal([], ⌜∃s⦁ s = ⋂{S | ∀e el⦁ List2Set el ⊆ S ⇒ mk_T_ex_rep (e, el) ∈ S}⌝);
```

The closure of the empty set under the mk_T_ex_rep constructor yields the set of all T_ex representations.
This set is used to introduce the type T_ex.

## The Type T_ex

To introduce the type T_ex, the theorem that the closure of the empty set under the mk_T_ex_rep constructor is non-empty is required.
This is straightforward as any byte sequence together with an empty list of T_ex representations is in the closure, ensuring non-emptiness.

Once the type is introduced the constructor and destructor over the representation type can be lifted to the new type, providing the functions mk_T_ex and dest_T_ex.

```sml
val T_ex_type_defn = new_type_defn (["T_ex_type_defn"], "T_ex", [],  T_ex_rep_non_empty_thm);
```

The types of the constructor and destructor are to be as follows:

```sml
val T_ex_type_defn_lemma = save_thm ("T_ex_type_defn_lemma",
    rewrite_rule [T_ex_type_defn] (inst_type_rule [(ⓣT_ex⌝, ⓣ'a⌝)] (∀_elim ⌜is_T_ex_rep⌝ type_defn_lemma4)));
```

```sml
set_goal([], ⌜
    ∃(rep_T_ex : T_ex → BS) (abs_T_ex : BS → T_ex)⦁
    (∀ a⦁ abs_T_ex (rep_T_ex a) = a)
        ∧ (∀ r⦁ is_T_ex_rep r ⇔ rep_T_ex (abs_T_ex r) = r)
        ∧ OneOne rep_T_ex
        ∧ (∀ a⦁ is_T_ex_rep (rep_T_ex a))⌝);
a (strip_asm_tac T_ex_type_defn_lemma);
a (∃_tac ⌜rep⌝ THEN ∃_tac ⌜abs⌝ THEN REPEAT strip_tac
    THEN TRY (asm_rewrite_tac[]));
a (asm_fc_tac[]);
save_cs_∃_thm(pop_thm());
```

```sml
ⓈHOLCONST
│   rep_T_ex : T_ex → BS;
│   abs_T_ex : BS → T_ex
├──────
│   (∀ a⦁ abs_T_ex (rep_T_ex a) = a)
│         ∧ (∀ r⦁ is_T_ex_rep r ⇔ rep_T_ex (abs_T_ex r) = r)
│         ∧ OneOne rep_T_ex
│         ∧ (∀ a⦁ is_T_ex_rep (rep_T_ex a))
■
```

The following definition is a place-holder for the actual definition of the constructor and destructor over the new type T_ex.
This is sufficient to allow the new Type T_ex to be introduced and and used in subsequent definitions, but will need to be replaced with a fuller definitions before proofs are attempted.

For concision in the presentation of T-expressions the alias `T` is introduced for the constructor `mk_T_ex`, this is effectively overloading the name already used for the BOOLean truth value, but since the latter is not a function, ambiguity is unlikely to arise.

```
stop;
set_flag("pp_show_HOL_types", true);
set_goal([], ⌜
    ∃(mk_T_ex : BS × T_ex LIST → T_ex) (dest_T_ex : T_ex → BS × T_ex LIST)⦁
    (∀ sxs⦁ dest_T_ex (mk_T_ex sxs) = sxs)⌝);
a (strip_asm_tac T_ex_type_defn_lemma);
a (∃_tac ⌜abs⌝ THEN ∃_tac ⌜rep⌝ THEN REPEAT strip_tac
    THEN TRY (asm_rewrite_tac[]));
a (asm_fc_tac[]);
save_cs_∃_thm(pop_thm());
```


```sml
ⓈHOLCONST
│   mk_T_ex : BS × T_ex LIST → T_ex;
│   dest_T_ex : T_ex → BS × T_ex LIST
├──────
│   ∀sxs⦁ dest_T_ex (mk_T_ex sxs) = sxs
■
declare_alias ("T", ⌜mk_T_ex⌝);
```

The type T_ex is the closure of the empty set under the constructor mk_T_ex (the first parameter being a byte sequence, and hence not required to be in the set, and the second a finite list of elements from the set).
The set of byte sequences with an empty list of T-expressions seed the iteration.
The set of representatives is then the closure of the empty set under the construction, which is the intersection of all sets closed under the construction.
The set of all byte sequences is thus closed, and therefore ensures that the closure exists and is a subset of that set (the type BS).

The new type can therefore be introduced as the intersection of the closed sets, together with the proof of non-emptiness.
The previously defined constructor and destructor over the representatives can then be lifted to the new type, and the required properties proved using the results on the representation type.

## Induction and Recursion over T-expressions

The type T_ex is to be the free algebra generated by the constructor mk_T_ex from the empty set of T-expressions.
It is therefore required to satisfy the following induction principle, which must be proven:

```sml
new_conjecture (["T_ex_induction_thm"], ⌜
    ∀P:T_ex → BOOL⦁
        (∀(s:STRING) (xs:T_ex LIST)⦁
            (∀x:T_ex⦁ ∀⋎L (map P xs)
            ⇒ P (mk_T_ex (s, xs))))
        ⇒ ∀ t⦁ P t⌝);
```

```sml
set_goal([],⌜
    ∀P:T_ex → BOOL⦁
        (∀(s:BS) (exs:T_ex LIST)⦁
            (∀x:T_ex⦁ ∀⋎L (map P exs)
            ⇒ P (mk_T_ex (s, xs))))
        ⇒ ∀ t⦁ P t⌝);

```

```sml
new_conjecture (["T_ex_prim_rec_thm"], ⌜
    ∀ f1 f2⦁ ∃⋎1 f⦁ ∀ bs tx txs bss⦁
        f (mk_T_ex (bs, [])) = f1 bs
    ∧   f (mk_T_ex (bs, Cons tx txs)) = f2 bs (map f (Cons tx txs))⌝);
```

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

```
Greek Letters
	Γ Δ Θ Λ Ξ Π Σ Υ Φ Ψ Ω
	α β γ δ ε ζ η θ ι κ λ μ ν ξ π ρ σ τ υ φ χ ψ ω
Logic: 	∧ ∨ ¬ ∀ ∃ ⦁ ╳ ≤ ≠ ≥ ∈ ∉ ⇔ ⇒
Set symbols: 𝔹 ℂ 𝔽 ℕ ℙ ℚ ℝ 𝕊 𝕌 ℤ ⊆ ∅ ⊂ ∩ ⋂ ∪ ⋃ ⊖
Arrows: → ⤖ ⤕ ⇻ ↔ ⤀ ⇸ ↣ ↦ ↠ ⤔
Formal Text Brackets: ⌜ ⌝ ⓣ ⓜ ⓩ Ⓢ ■ ┌ └ ╒ ├
Padding symbols	│ ─ ═  Index Brackets ⦏ ⦎
Bracketing symbols: ⟨ ⟩ ⟦ ⟧ ⦇ ⦈
Subscription and Superscription: ⋎ ⋏ ↗ ↘ ↕ Underlining: ⨽ ⨼
Relation, Sequence and Bag Symbols:  ⩥ ▷ ⩤ ◁ ⁀ ↾ ↿ ⊕ ⊎ ⨾ ∘
Miscellaneous: ⊢ ⦂ ≜ ⊥ ⊖
```
