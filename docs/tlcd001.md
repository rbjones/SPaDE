# SPaDE formal specification - Overview and AbstractSyntax

This is the first of a series of documents intended to provide formal specifications for the SPaDE system, in particular for the representation of knowledge in SPaDE.

It is written in ProofPower HOL to enable its checking and use to be undertaken in advance of support for HOL in SPaDE, with the intention that it will in due course be ported into SPaDE itself and support reasoning by SPaDE about itself at all levels.

The initial versions developed in HOL will be worked in the context of a fairly well-populated ProofPower HOL database, but will use the smallest context available (the theory basic-hol) and will be written to avoid any but the most elementary features, so, in addition to it being intended to specify the structure of SPaDE repositories, it will also be intended as a reworking of the HOL primitive theories for SPaDE.

In relation to those primitive theories, the main thrust of the changes is to place front and center reflexive reasoning about SPaDE itself, rather than, say formalising the real numbers, as well as the strengthening of the axiom infinity to underpin SPaDE's status as a Universal Foundational Institution (see tlph010.md).
Thus, for example, the axioms are intended to deliver sufficient strength to embed the LEAN language.
The axiom of choice in SPaDE may be stated as the existence of initial strict well-orderings of any collection.

```sml
new_SPaDE_theory ("tlcd001", "SPaDEroot", []);
```

## Axiom of Choice

Choice is axiomatised as the existence of initial strict well-orderings of any type.
We do not supply separate definitions of the usual constituent concept for the purposes of the expressing choice.
This decision is subject to review of course.

```sml
declare_infix (300, "<<");
```

```
Logic: ∧ ∨ ¬ ∀ ∃ ⦁ × ≤ ≠ ≥ ∈ ∉ ⇔ ⇒
```

```sml
ⓈHOLCONST
│ transitive: ('a → 'a → BOOL) → BOOL
├──────
│ ∀ $<<⦁ transitive $<< ⇔ ∀x y z⦁  (x << y ∧ y << z) ⇒ x << z
■
```

```sml
ⓈHOLCONST
│ linear_order: ('a → 'a → BOOL) → BOOL
├──────
│ ∀ $<<⦁ linear_order $<< ⇔
|   transitive $<< ∧ 
|   ∀x y⦁  x = y ∨ x << y ∨ y << x
■
```

```sml
ⓈHOLCONST
│ well_founded: ('a → 'a → BOOL) → BOOL
├──────
│ ∀ $<<⦁ well_founded $<< ⇔
│       ∀p⦁ (∃x⦁ p x) ⇒ 
│           (∃y⦁ p y ∧ ∀z⦁ p z ⇒ z = y ∨ y << z)
■
```

```sml
ⓈHOLCONST
│ well_order: ('a → 'a → BOOL) → BOOL
├──────
│ ∀ $<<⦁ well_order $<< ⇔
│       linear_order $<< ∧ well_founded $<<
■
```

```sml
ⓈHOLCONST
│ strict: ('a → 'a → BOOL) → BOOL
├──────
│ ∀ $<<⦁ strict $<< ⇔ ∀x⦁ ¬(x << x)
■
```

```sml
ⓈHOLCONST
│ one_one: ('a → 'b → BOOL) → BOOL
├──────
│ ∀ f⦁ one_one f ⇔ ∀x y⦁  f x = f y ⇒ x = y
■
```

```sml
ⓈHOLCONST
│ initial: ('a → 'a → BOOL) → BOOL
├──────
│ ∀ $<<⦁ initial $<< ⇔ ¬ ∃f x⦁ one_one f ∧ ∀y⦁ f y << x
■
```

```sml
ⓈHOLCONST
│ iswo: ('a → 'a → BOOL) → BOOL
├──────
│ ∀ $<<⦁ iswo $<< ⇔
│       initial $<< ∧ strict $<< ∧ well_order $<<
■
