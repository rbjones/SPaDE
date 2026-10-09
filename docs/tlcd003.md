# Choice, Strong Infinity and Reflection

This document is a preliminary exploration of some of the points of variance in the primitive logic of HOL which are under consideration for SPaDE.
Except for the adoption of stronger than usual axioms of infinity (essentially, large cardinal axioms), these are not intended to change the derivability relationship.
The theorems of HOL should be unchanged, but the proofs of them obtainable by the primitive inference rules will differ.

This document explores a polymorphic theory of strong infinity in ProofPower HOL. It introduces a new type constructor and asserts that the cardinality of the new type is inaccessibly greater than its parameter type.

The possible alteration to the axiom of choice is merely a device to streamline the bootstrap which gets SPaDE repositories off the ground.
The idea is that instead of asserting choice is its most elementary form, we assert the existence of initial strict well-orderings, as statement equivalent to the more elementary version which side-steps the need to actually prove the existence of those well orderings (which are use in stating the strong infinity axioms).
Of course, this does introduce greater risk of soundness compromising cock-ups, since if I get the definition wrong the choice axiom might then be false.

The third area we might go into here is reflection, which involves the ability of the system to reason about its own statements and proofs. This is a more advanced topic and will be explored in subsequent documents.
This does ultimately depend on a full formulation of the syntax and deductive system of SPaDE HOL but a generic treatment of reflection principles is probably possible building only on the theory of T-expressions which is in SPaDEroot.

The theory is a child of SPaDEroot and is named tlcd003.

```sml
new_SPaDE_theory("tlcd003", "SPaDEroot", []);
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
