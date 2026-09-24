# Task: SPaDE specifications corresponding to spc001–spc005

## Purpose

Recast the ProofPower series `spc001.pp`–`spc005.pp` as SPaDE specifications. The SPaDE documents are markdown with `hol` fences, as [tlcd001.md](../tlcd001.md) is. They are part of SPaDE. The ProofPower sources and the `retro/` directory are bootstrap, not part of SPaDE.

The deductive system is unchanged. What changes is the form, the provenance, the way the theories are introduced into the ProofPower database used by SPaDE, and the requirement that the inference rules be executable.

## First step

The ProofPower database used by SPaDE already has `spc001`–`spc005` loaded. A SPaDE theory of the same name fails unless the original is deleted first.

The HOL in the new documents therefore begins by deleting those theories, children before parents:

1. `spc005` (parent `spc004`)
2. `spc004` (parent `spc002`)
3. `spc003` (parent `spc001`)
4. `spc002` (parent `spc001`)
5. `spc001` (parent `fin_set`)

ProofPower provides `delete_theory`, and `force_delete_theory` where a theory still has children. This deletion is the first formal text in the series. No new theory is introduced before it has run.

## The documents

One markdown document for each of `spc001`–`spc005`, under `docs/`, processed by `docs/tlci001.mkf` so that `make` in `docs/` strips the `hol` fences to `.sml`.

Each document:

- Acknowledges the ProofPower source it is derived from, by name (`spc00n.pp` in the ProofPower source `src/hol`).
- States what has been changed. That account is taken from this task description, and from any later task description that adds a change. It is not left for the reader to infer.
- Keeps the deductive system of the source.
- States the inference rules so that they can be executed. SPaDE is to prove a derived rule sound and then run it. Those derived rules are the earliest reflective self-improvement.

`make` in `docs/` produces the `.sml`. ProofPower then checks that the script is well-formed. Acceptance by ProofPower is not a check of correctness. Correctness is a further check, by a more intelligent reading of the specification against this task.

## Material under kr/

A large part of the specifications in `kr/` is architectural. It is input to this work. The likely outcome is a new specification in `docs/` which supersedes it. Promotion of an existing `kr/` document into `docs/` is the alternative, when the document is already in the SPaDE form. Specifications in `kr/` written for HOL4 are not the form of the new architectural HOL. New architectural HOL is ProofPower HOL in markdown.

## Not in this task

Do not rewrite `retro/`. Do not treat ProofPower as a SPaDE deliverable. Do not start this task until the description is on `main`.

---

Document ID: amtd006
Author: Grok Build (Grok 4.7)
Status: In progress
Chat log: [amcl003.md](amcl003.md)
