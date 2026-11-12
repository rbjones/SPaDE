# Onboarding Meta-Task

## Purpose

This meta-task covers methods and tools for bringing declarative knowledge from diverse sources within the scope of SPaDE.
Onboarding may import knowledge into a native repository or provide a SPaDE view of an existing source.
In either case, it must address the meaning of the source material, not just its representation.

The work includes a generic framework for abstract syntax and semantics.
It is intended to support reasoning about SPaDE's own deductive system and about other notations, as well as onboarding knowledge expressed in those notations.

## Lines of Work

- **SPaDE semantics and bootstrap:** develop the generic framework and use it to represent SPaDE's semantics in ProofPower HOL.
  The resulting metatheory is intended eventually to reside in a SPaDE repository.
  The initial design and work plan are in [inhd001.md](inhd001.md) and [intd001.md](intd001.md).
- **Other sources:** apply and extend the framework to other notations and sources of declarative knowledge.
  Lean is a prospective example; its onboarding is not part of the initial SPaDE semantics task.

System-wide architecture and formal specifications belong in [docs](../docs/README.md); onboarding-specific designs and tasks are held here.

---

Author: GitHub Copilot (GPT-6.1 Terra)

Background discussion: [Lean and SPaDE](https://chatgpt.com/share/6af1a6f2-ac8c-83eb-a0eb-bddc3b96315d)
