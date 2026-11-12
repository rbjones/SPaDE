# Task Description: SPaDE Semantic Embedding in ProofPower HOL

## Purpose

Develop a generic semantic framework and an initial representation of SPaDE's own semantics in ProofPower HOL.
This supports SPaDE's reflexive metatheory and prepares semantic onboarding of other notations.
The starting sketch is [inhd001.md](inhd001.md).
This is a plan for future work; it does not assert that the framework or embedding is already implemented.

## Inputs and Placement

- [tltd004.md](../docs/tltd004.md) and [tlcd004.md](../docs/tlcd004.md): the T-expression theory.
- [tltd001.md](../docs/tltd001.md) and [tlcd001.md](../docs/tlcd001.md): the generic abstract syntax and SPaDE formal specification.
- [tlcd002.md](../docs/tlcd002.md): the bootstrap theory and the intended transfer boundary.
- [tlcd003.md](../docs/tlcd003.md): the exploration of choice and strong infinity.
- [ProofPower's spc002](https://www.lemma-one.com/ProofPower/doc/spc002.pdf): a reference for formal HOL semantics.
- [amms012.md](../docs/admin/amms012.md) and [ampd012.md](../docs/admin/ampd012.md): the method and procedure for ProofPower HOL specifications.

System-wide formal specifications are to be written in the `docs/tlcd` series, not in this onboarding directory.
Before commissioning each formal stage, identify its specification document, theory name, parents, assumptions and reproducible ProofPower check.

## Proposed Stages

1. **Refine the design.** Identify the generic semantic structures and the SPaDE-specific instance, including syntactic categories, contexts, binding, semantic domains, assignments and interpretation.
   Record the initial fragment, its proof obligations and the intended theory dependencies.
   Review the design before committing to formal definitions.
   This stage can proceed while the T-expression theory is being completed.
2. **Establish the needed syntax.** Coordinate with the existing T-expression and abstract-syntax tasks rather than duplicate them.
   Obtain the constructors and well-formedness and typing conditions needed for the chosen fragment.
3. **Specify the semantics.** Define the agreed generic framework and the SPaDE instance in ProofPower HOL.
   Start with types, typed variables and application, then add constants, abstraction, context constraints and satisfaction.
   Parameterize the development by the semantic structures and assumptions it needs.
4. **Prove initial properties.** For a stated fragment containing at least typed variables and application, prove that interpretation respects typing and establish semantic soundness for at least one identified inference rule.
   State the model and valuation assumptions; exhibit a suitable model for the fragment or make model existence an explicit assumption.
   Record the remaining obligations, including substitution and the extension to the full deductive system.
5. **Extend and transfer.** Address the semantics and proof obligations for strong infinity and reflection as those parts of SPaDE are specified.
   Record the theories, assumptions and proof dependencies needed to transfer and recheck the metatheory in a SPaDE repository.
   The generic framework can subsequently be exercised with a different notation, such as Lean.

## Completion of a Formal Stage

The stage's specification, theory and parents must be identified and integrated into the relevant build as prescribed by [ampd012.md](../docs/admin/ampd012.md).
ProofPower must load the specification without errors and check the proofs claimed for that stage.
The result must identify its assumptions, any unproved conjectures and the remaining work; conditional soundness must not be presented as a proof that a model exists.

This task does not commission a Lean importer, a translation of Chain Theory, or an implementation of the SPaDE deductive kernel.

---

Author: GitHub Copilot (GPT-6.1 Terra)

Background discussion: [Lean and SPaDE](https://chatgpt.com/share/6af1a6f2-ac8c-83eb-a0eb-bddc3b96315d)
