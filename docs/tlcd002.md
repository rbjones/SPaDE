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

```sml
structure SPaDEroot = struct
```

### SPaDE Theory Prelude

In this section a single procedure is defined to set up a theory prior to presenting its formal content.

```
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
end; (* of structure SPaDEroot *)

open SPaDEroot;
```

## SPaDEroot Theory

```sml
new_SPaDE_theory ("SPaDEroot", "rbjmisc", []);
force_new_pc "'SPaDEroot";
set_pc "rbjmisc";
```

## Some HOL Constants

## Theorems

### Lists

```sml
set_goal([], ⌜∀f⦁ Map f [] = []⌝);
a (strip_tac);
a (rewrite_tac[get_spec ⌜Map⌝]);
val Map_nil_thm = save_pop_thm "Map_nil_thm";
```

### OneOne

```sml
new_conjecture (["OneOne_left_inverse_thm"],
    ⌜∀ f:'a → 'b⦁ OneOne f ⇒ ∃g:'b → 'a⦁ ∀x:'a⦁ g o f = λx⦁ x⌝);
```

```sml
set_goal([], ⌜∀ f:'a → 'b⦁ OneOne f ⇒ ∃g:'b → 'a⦁ ∀x:'a⦁ g o f = λx⦁ x⌝);
a (strip_tac THEN rewrite_tac[get_spec ⌜OneOne⌝]);
a (REPEAT strip_tac);
a (∃_tac ⌜λx:'b⦁ ε y:'a⦁ f y = x⌝);
a (REPEAT strip_tac);
a (rewrite_tac[ext_thm, get_spec⌜$o:('b→'a)→('a→'b)→('a→'a)⌝]
    THEN strip_tac);
a (LEMMA_T ⌜∃y⦁ f y = f x⌝ asm_tac);
a (∃_tac ⌜x⌝ THEN rewrite_tac[]);
a (asm_fc_tac [simple_∃_ε_conv ⌜∃y⦁ f y = f x⌝]);
a (asm_tac (rewrite_rule [asm_rule ⌜∃ y⦁ f y = f x⌝] (simple_∃_ε_conv ⌜∃y⦁ f y = f x⌝)));
a (all_asm_fc_tac[]);
val OneOne_left_inverse_thm = save_pop_thm "OneOne_left_inverse_thm";
```

## Proof Contexts

```sml
add_rw_thms [Map_nil_thm] "'SPaDEroot";
commit_pc "'SPaDEroot";
force_new_pc "SPaDEroot";

merge_pcs ["rbjmisc", "'SPaDEroot"] "SPaDEroot";
commit_pc "SPaDEroot";

force_new_pc "SPaDEroot1";
merge_pcs ["rbjmisc1", "'SPaDEroot"] "SPaDEroot1";
commit_pc "SPaDEroot1";
```

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

set_flag ("pp_show_HOL_types", false);
```
