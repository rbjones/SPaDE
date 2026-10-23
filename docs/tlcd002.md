# The SPaDEroot Theory

The SPaDE root theory provides the prelude used by the other SPaDE specifications in ProofPower HOL, and a way to supply a consistency proof before a constant specification is introduced.

The theory of T-expressions is separate. It is the theory `T_ex`, specified in [tlcd004.md](tlcd004.md).

This theory forms a boundary between those parts of the SPaDE system specification which will be transferred materially unchanged into the core SPaDE native repository after first being developed and verified within the ProofPower environment, and those parts beneath them which here rest on structures provided by ProofPower which are liable to be reworked.
The metatheory articulated as the SPaDE architecture (in theories which descend from this SPaDE root theory), is that of the SPaDE system, and will eventually be transferred into the core SPaDE native repository.

It also represents a boundary beneath which may be found details of the implementation of features of SPaDE (such as the knowledge repository) which are not architectural or standardised, are not exposed on the MCP interface and are likely to be varied in diverse implementations of SPaDE repositories.
T-expressions appear in [tlcd004.md](tlcd004.md), in the Python interfaces between SPaDE subsystems, and, represented in JSON, in the MCP protocol which delivers SPaDE to the models it serves.
They are therefore architectural, whereas the details of how the T-expressions constituting a SPaDE repository are stored and manipulated may vary between different implementations, and it is intended that existing data structures such as SQL databases can be incorporated into an diasporic SPaDE repository using a suitable implementation of the knowledge repository interface.

This document is presented in the following parts:
- [Some SML Procedures](#some-sml-procedures) - to simplify the presentation of the SPaDE formal specifications.
- [Some HOL Constants](#some-hol-constants)

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
new_SPaDE_theory ("SPaDEroot", "rbjmisc", []);
set_pc "rbjmisc";
```

### Pre-proving Consistency Theorem

I had intended to minimise the required context for the SPaDE specifications (and hence the core theories required for bootstrapping to SPaDE repositories), but this will slow down the specification and early prototyping too much, so context minimisation, making the core HOL theories for SPaDE as slim and efficient as possible, will be deferred for the time being.
This section is now temporarily redundant since the material is included in the rbjmisc theory (in the retro/np directory) which the specifications will build on pro-tem.
I have left it while removing the "sml" from the formal sections so that they do not get stripped and executed.

For the sake of getting ProofPower theory listings nice, it is desirable when a consistency theorem is needed for a constant definition to prove it before introducing the definition so that it can be used by the automatic consistency prover.
This is only necessary when the form of the specification defies the talents of the automatic consistency prover.

First we provide a place and a procedure to save the consistency theorem so that it can be retrieved and used by the consistency prover:

```
val saved_cs_∃_thm = ref t_thm;

fun save_cs_∃_thm thm = (saved_cs_∃_thm := thm; thm);
```

Then we need a special partial proof context with a consistency prover which knows to look for the consistency proof in this special place.

This is the consistency prover which refers to the saved consistency theorem (conversion):

```
fun savedthm_cs_∃_conv x =
	if x =$ (concl(!saved_cs_∃_thm))
	then (⇔_t_intro (!saved_cs_∃_thm)) handle _ => (* eq_ *) refl_conv x
	else (* eq_ *) refl_conv x;
```

Store the above in a proof context.

```
val _ = force_new_pc ⦏"'prove_∃_⇒_conv"⦎;
val _ = set_cs_∃_convs [prove_∃_⇒_conv, ONCE_MAP_C (pure_once_rewrite_conv [let_def] THEN_C (MAP_C β_conv))] "'prove_∃_⇒_conv";
val _ = commit_pc "'prove_∃_⇒_conv";
```

```
val _ = force_new_pc "'savedthm_cs_∃_proof";
val _ = set_cs_∃_convs [prove_∃_⇒_conv, savedthm_cs_∃_conv] "'savedthm_cs_∃_proof";
val _ = set_pr_conv basic_prove_conv "'savedthm_cs_∃_proof";
val _ = set_pr_tac basic_prove_tac "'savedthm_cs_∃_proof";
val _ = commit_pc "'savedthm_cs_∃_proof";
```

## Some HOL Constants

## Useful Symbols

These are included here for convenience when humans are writing HOL specifications and don't know a better way than cut and paste to get them in their specifications (me at present!).
It also provides information to agents about the symbols available for use in HOL specifications.

```
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