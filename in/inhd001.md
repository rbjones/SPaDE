# SPaDE Semantics in ProofPower HOL: A Sketch

## Purpose

This is a preliminary design for representing the semantics of SPaDE's logical system in ProofPower HOL.
It is an early application of a generic framework for the syntax and semantics of declarative notations.
The framework should support reasoning about SPaDE itself and, later, onboarding and metatheoretic reasoning about other notations.

ProofPower HOL is the present host or *metalanguage*; SPaDE's logical system is the *object language* being described.
The metatheory is to be developed in ProofPower before SPaDE can support it, and eventually transferred into a SPaDE repository.
The existing specification boundary and bootstrap context are described in [tlcd002.md](../docs/tlcd002.md).

## Generic Syntax and Semantics

The theory of T-expressions, [tlcd004.md](../docs/tlcd004.md), is intended to provide the underlying representation of abstract syntax.
An instance for a notation identifies its syntactic categories, constructors, binding and well-formedness conditions.
SPaDE types, terms, contexts and deductive structures are an initial instance; other notations can have different categories and binding rules.

The generic semantic framework must also accommodate each notation's semantic domains, interpretations and assignments, and the meanings of its expressions in context.
It must cover values of types and terms as well as truth and satisfaction.
The framework should permit different kinds of semantic domain rather than require every notation to use one fixed value type.
T-expressions represent syntax and can represent the syntax of semantic definitions; semantic values themselves may be infinite structures or functions.

The set-theoretic treatment in [ProofPower's spc002](https://www.lemma-one.com/ProofPower/doc/spc002.pdf) is a reference for the SPaDE instance.
It describes a semantic universe using a polymorphic HOL type and a membership relation, and specifies interpretations and models relative to such a universe.
This is a starting point, not a requirement that every other notation use exactly the same semantic construction.

## A SPaDE Instance

A SPaDE interpretation assigns meanings to type constructors and constants.
Together with assignments to type and term variables, it determines values of well-formed types and terms.
An interpretation is a model of a context when it satisfies that context's constraints; boolean terms and sequents can then be interpreted for admissible assignments.
The instance must account for polymorphism, binding, substitution and the intended SPaDE contexts and inference rules.

For illustration only, let `node(label, children)` stand for the proposed T-expression constructor.
The labels and the representation of binding have not been settled:

```text
Var(x, ty) = node("Var", [node(x, []), ty])
App(f, a)  = node("App", [f, a])

value(M, theta, rho, Var(x, ty)) = rho(x, ty)
value(M, theta, rho, App(f, a))  =
    apply_M(value(M, theta, rho, f), value(M, theta, rho, a))
```

Here `M` is an interpretation, `theta` assigns type variables, and `rho` assigns suitably typed values to term variables for that type assignment.
The equations apply to well-formed, well-typed expressions and admissible assignments.
`apply_M` is application in the semantic universe; it is not necessarily ordinary application of a HOL function.
The definitions for constants, abstractions, types, contexts and satisfaction remain to be specified.

## Metatheory and Embedding

The SPaDE instance should support proofs that interpretation respects typing and substitution and that the specified inference rules preserve validity.
For example, a soundness statement would say that if a sequent is derivable in a context, then every model of that context and every admissible assignment satisfying its hypotheses also satisfies its conclusion.
Such results are conditional on the stated model and logical assumptions; an empty class of models would make validity vacuous.

The semantic embedding is the representation of SPaDE's syntax and its interpretation within HOL, not merely an encoding of its syntax or a direct translation of every expression into a native HOL expression.
For an embedding between notations, the framework should make explicit the correspondence between contexts and interpretations and what it means to preserve the values of expressions and the truth of sentences.
Checking a formal statement in ProofPower does not by itself establish that its definitions capture the intended SPaDE semantics.

## Strength and Transfer

The intended HOL foundational institution is a family of systems of increasing semantic strength, not a single fixed universe; see [tlad001.md](../docs/tlad001.md#foundational-institution).
A suitably stronger level can describe the semantics of a weaker one.
The strong-infinity work in [tlcd003.md](../docs/tlcd003.md) is intended to provide the strength needed for embeddings including Lean.
For each semantic development, the required universe properties, axioms and any model-existence assumptions should be stated explicitly.
Defining a class of models and proving conditional properties can precede establishing that a suitable model exists.

The specification and its dependencies should be kept suitable for eventual transfer across the [SPaDEroot](../docs/tlcd002.md) boundary.
Transfer must preserve the relevant contexts and assumptions and re-establish or check the results in the target system; a ProofPower result is not automatically a SPaDE theorem.
The general universality claim concerns semantic expressiveness, as discussed in [tlph008.md](../docs/tlph008.md); the SPaDE and Lean instances would contribute to its examination but would not alone establish it.

The proposed stages are in [intd001.md](intd001.md).

---

Author: GitHub Copilot (GPT-6.1 Terra)

Background discussion: [Lean and SPaDE](https://chatgpt.com/share/6af1a6f2-ac8c-83eb-a0eb-bddc3b96315d)
