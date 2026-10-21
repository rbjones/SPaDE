# The SPaDEroot Theory

The SPaDE root theory provides the foundational elements necessary for the formal specification of the SPaDE system. It includes the theory of T-expressions, which are tuple expressions, a minor elaboration of LISP S-expressions.
The theory of T-expressions underpins the representation of abstract syntax and the structure of types and terms within SPaDE.

This theory forms a boundary between those parts of the SPaDE system specification which will be transferred materially unchanged into the core SPaDE native repository after first being developed and verified within the ProofPower environment, and those parts beneath them which here rest on structures provided by ProofPower which are liable to be reworked.
The metatheory articulated as the SPaDE architecture (in theories which descend from this SPaDE root theory), is that of the SPaDE system, and will eventually be transferred into the core SPaDE native repository.

It also represents a boundary beneath which may be found details of the implementation of features of SPaDE (such as the knowledge repository) which are not architectural or standardised, are not exposed on the MCP interface and are likely to be varied in diverse implementations of SPaDE repositories.
T-expressions appear not only in this specification, but also in the python interfaces between SPaDE subsystems and (represented in JSON) in the MCP protocol which is the primary means of delivering SPaDE capabilities to the LLMs which SPaDE is designed to serve.
They are therefore architectural, whereas the details of how the T-expressions constituting a SPaDE repository are stored and manipulated may vary between different implementations, and it is intended that existing data structures such as SQL databases can be incorporated into an diasporic SPaDE repository using a suitable implementation of the knowledge repository interface.

This document is presented in the following parts:
- [Some SML Procedures](#some-sml-procedures) - to simplify the presentation of the SPaDE formal specifications.
- [Some HOL Constants](#some-hol-constants)
- [A Byte Sequence Packing Method](#the-byte-sequence-packing-method)
- [The Type oF T-expressions](#the-type-of-t-expressions)

All parts of this document are subject to further development as the needs of the SPaDE specifications evolve.

## Some SML Procedures

### SPaDE Theory Prelude

In this section a single procedure is defined to set up a theory prior to presenting its formal content.

```sml
fun force_new_theory name =
  let val _ = force_delete_theory name handle _ => ();
  in new_theory name
end;
```

```sml
fun new_SPaDE_theory (theory_name, parent, other_parents) =
    let val _ = open_theory parent;
        val _ = force_new_theory theory_name;
    in  map new_parent other_parents
end;
```

```sml
new_SPaDE_theory ("SPaDEroot", "hol", []);
set_pc "hol";
```

### Pre-proving Consistency Theorem

For the sake of getting ProofPower theory listings nice, it is desirable when a consistency theorem is needed for a constant definition to prove it before introducing the definition so that it can be used by the automatic consistency prover.
This is only necessary when the form of the specification defies the talents of the automatic consistency prover.

First we provide a place and a procedure to save the consistency theorem so that it can be retrieved and used by the consistency prover:

```sml
val saved_cs_∃_thm = ref t_thm;

fun save_cs_∃_thm thm = (saved_cs_∃_thm := thm; thm);
```

Then we need a special partial proof context with a consistency prover which knows to look for the consistency proof in this special place.

This is the consistency prover which refers to the saved consistency theorem (conversion):

```sml
fun savedthm_cs_∃_conv x =
	if x =$ (concl(!saved_cs_∃_thm))
	then (⇔_t_intro (!saved_cs_∃_thm)) handle _ => (* eq_ *) refl_conv x
	else (* eq_ *) refl_conv x;
```

Store the above in a proof context.

```sml
val _ = force_new_pc ⦏"'prove_∃_⇒_conv"⦎;
val _ = set_cs_∃_convs [prove_∃_⇒_conv, ONCE_MAP_C (pure_once_rewrite_conv [let_def] THEN_C (MAP_C β_conv))] "'prove_∃_⇒_conv";
val _ = commit_pc "'prove_∃_⇒_conv";
```

```sml
val _ = force_new_pc "'savedthm_cs_∃_proof";
val _ = set_cs_∃_convs [prove_∃_⇒_conv, savedthm_cs_∃_conv] "'savedthm_cs_∃_proof";
val _ = set_pr_conv basic_prove_conv "'savedthm_cs_∃_proof";
val _ = set_pr_tac basic_prove_tac "'savedthm_cs_∃_proof";
val _ = commit_pc "'savedthm_cs_∃_proof";
```

## Some HOL Constants

## A Byte Sequence Packing Method

To introduce the type of T-expressions (We'd better use the name T-ex for brevity) we must identify a representation for T-expressions over which the required operations are definable.

I'm thinking here in terms of byte sequences.
In ProofPower HOL the type CHAR represents a single byte (UNICODE characters are represented using utf8).
The type STRING is an abbreviation for CHAR LIST.

T-expressions are a free algebra generated from the empty set by an operator which takes a finite sequence (LIST) of bytes (CHARs) (which is a STRING) and a finite (possibly empty) sequence of T-expressions.
Byte sequences will suffice as a representation if we can find an injection from lists of byte sequences into byte sequences (since all the T-expressions supplied to the constructor are themselves represented as byte sequences.)

The required injection is obtained by converting each byte sequence in the list into a null terminatedd byte sequence (NTBS), using an escape character to handle any embedded nulls.
We use the character X`01` as escape character.
Null is of course the byte X`00`.
The escape character is also used to escape itself, if it appears in the STRING being packed before another escape or null character (but not otherwise).
On unpacking therefore, any escape character preceding another escape or null character is discarded, and the following character is copied to the output.

### Byte Sequence Packing Functions

In the following, pack_bytes must be an injection and unpack_bytes must be a left-inverse of pack_bytes.
In HOL it could be defined as a left inverse, but we want the functionality of SPaDE to be defined constructively so that it is potentially executable.

The algorithm to be used for packing is described in 
[../kr/krdd004.md#encoding-and-decoding-ntbs-and-related-data-types](../kr/krdd004.md#encoding-and-decoding-ntbs-and-related-data-types).
This is not "architectural" but is specific to the "SPaDE" native repositories and need not be used in any other concrete representation of SPaDE knowledge bases.
The architecture mandates only the T_ex structure and the representation of knowledge above that level.

In the terminology of that document, pack byes should concatenate the null-terminated byte sequence representations of each byte sequence in the list (but the whole should not then be converted into null terminated form, though in the SPaDE native repositories it would be stored null terminated).
unpack_bytes is then its inverse.

The algorithm is formally specified as follows:

For the purposes of the architectural specifications, we need only to know that unpack_bytes is a right-inverse of pack_bytes, but in order to establish the consistency of that requirement we need a more explicit description of a suitable algorithm (which properly belongs in the kr subsystem).
The subscript `_w` indicates that these are the "witnesses" for the existence of suitable packing and unpacking functions.

```sml
ⓈHOLCONST
│   pack_bytes_w : STRING LIST → STRING;
│   unpack_bytes_w : STRING → STRING LIST
├──────
│   T
■
```


```sml
ⓈHOLCONST
│   pack_bytes : STRING LIST → STRING;
│   unpack_bytes : STRING → STRING LIST
├──────
│   ∀s:STRING⦁ ∀xs:STRING LIST⦁ unpack_bytes (pack_bytes xs) = xs
■
```

## The Type of T-expressions

The type of T-expressions has as its representation type the strings in the range of the injection `pack_bytes` applied to arbitrary lists of byte sequences.

To define the type of T-expressions, we introduce a new type definition in HOL using the `new_type_defn` function. This ensures that the type `T-ex` is properly represented by the strings obtained from the `pack_bytes` injection applied to lists of byte sequences.
The representation for the type is the range of the `pack_bytes` injection applied to lists of byte sequences, and the type definition required the theorem that the range is non-empty.

```sml
val T_ex_non_empty_thm = tac_proof ( ([], ⌜∃x:STRING⦁
        (λx:STRING⦁ ∃xs:STRING LIST⦁ x = pack_bytes xs)
        x⌝),
        (∃_tac ⌜pack_bytes[]⌝
        THEN rewrite_tac[]
        THEN ∃_tac ⌜[]⌝
        THEN rewrite_tac[]));


val T_ex_defn = new_type_defn (["T_ex_def"], "T_ex", [],
    T_ex_non_empty_thm);
rewrite_rule [get_spec ⌜TypeDefn⌝] T_ex_defn;
```

```sml
ⓈHOLCONST
│   mk_T_ex : STRING × T_ex LIST → T_ex;
│   dest_T_ex : T_ex → STRING × T_ex LIST
├──────
│   ∀s:STRING⦁ ∀xs:T_ex LIST⦁ dest_T_ex (mk_T_ex (s, xs)) = (s, xs)
■
```

## Useful Characters

```

## Useful Symbols

These are included here for the convenience when humans are writing HOL specifications and don't know a better way than cut and paste to get them in their specifications (me at present!).
This section will probably disappear when I get my act together.

Greek Letters
	Γ Δ Θ Λ Ξ Π Σ Υ Φ Ψ Ω
	α β γ δ ε ζ η θ ι κ λ μ ν ξ π ρ σ τ υ φ χ ψ ω
Logic: 	∧ ∨ ¬ ∀ ∃ ⦁ × ≤ ≠ ≥ ∈ ∉ ⇔ ⇒
Set symbols: 𝔹 ℂ 𝔽 ℕ ℙ ℚ ℝ 𝕊 𝕌 ℤ ⊆ ∅ ⊂ ∩ ⋂ ∪ ⋃ ⊖
Arrows: → ⤖ ⤕ ⇻ ↔ ⤀ ⇸ ↣ ↦ ↠ ⤔
Formal Text Brackets: ⌜ ⌝ ⓣ ⓜ ⓩ Ⓢ ■ ┌ └ ╒ ├
Padding symbols	│ ─ ═  Index Brackets ⦏ ⦎
Bracketing symbols: ⟨ ⟩ ⟦ ⟧ ⦇ ⦈
Subscription and Superscription: ⋎ ⋏ ↗ ↘ ↕ Underlining: ⨽ ⨼
Relation, Sequence and Bag Symbols:  ⩥ ▷ ⩤ ◁ ⁀ ↾ ↿ ⊕ ⊎ ⨾ ∘
Miscellaneous: ⊢ ⦂ ≜ ⊥ ⊖
```