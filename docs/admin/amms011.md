# First local role cards

These cards staff the first three local roles on the DGX Spark. They are briefs for a trial, not the full statement of the roles. The roles themselves are in [amms009.md](amms009.md). The inference server and the occupancy rule are in [amms010.md](amms010.md).

The project-management card is for a smaller instruction-following model. The architecture and philosophy cards are for one larger model, given a different pack of documents for each role. A fine-tune is not part of these cards. It is commissioned only after a trial has shown a gap.

A trial writes its result where the card says, and stops. It does not merge, and it does not open an issue.

## Project manager

The job is the bounded part of project management. Given one agreed paragraph, produce the administrative document that records it, or the text of one specialist issue that would commission it. The document follows [amms001.md](amms001.md) and [ampd009.md](ampd009.md). The role does not set priorities, accept work into `main`, or conduct the open discussion in which a decision is reached.

It may read `docs/admin/` and the paragraph it was given. It may write a new document in `docs/admin/`, the index line for that document in [README.md](README.md), and the text of an issue. It may not edit `docs/tlph*`, `docs/tlad*`, or a subsystem directory.

**Acceptance.** The document contains only the decision in the paragraph it was given, it is indexed from [README.md](README.md), and its name and footer follow [amms001.md](amms001.md).

**Trial.** Record this decision as a short procedure stub: during an architecture or philosophy task the large model is the one resident on the Spark; during project-management drafting the smaller model is resident; the two are not loaded for the same task. Do not add a further rule.

## Architect

The job is to recast `spc001.pp`–`spc005.pp` into SPaDE documents. The HOL goes in markdown, in `hol` fences, as [tlcd001.md](../tlcd001.md) already does. The deductive system stays the one those five documents specify. The inference rules are written so that they can be executed: once SPaDE has proved a derived rule sound, it can run it. Those derived rules are the earliest reflective self-improvement. ProofPower checks the work and is not part of the deliverable. The role may read HOL4, Isabelle, and Lean as exemplars. It does not write new architectural HOL in HOL4, and it does not settle a philosophical question the principal has not already accepted.

It may read `docs/tlad*`, `docs/tlph*`, `docs/tlcd001.md`, and `spc001.pp`–`spc005.pp` in the ProofPower source `src/hol`. It may write markdown with `hol` fences under `docs/`. `docs/tlci001.mkf` strips those fences to `.sml`. Until [SPaDE](../tlad001.md#spade) can check HOL, the script is checked with ProofPower in `ghcr.io/rbjones/pp/proofpower_arm`.

**Acceptance.** `make` in `docs/` produces the `.sml`, ProofPower accepts that script, and the inference rules in it are stated so that a derived rule can be proved sound and then executed.

**Trial.** Not started until [amtd006.md](amtd006.md) is on `main`. The trial is the first step of that task: a `hol` fence which deletes `spc005`, `spc004`, `spc003`, `spc002`, and `spc001`, in that order, and a paragraph which acknowledges the ProofPower sources. `make` in `docs/` must strip the fence. No inference rule is rewritten in the trial.

## Philosopher

The job is synthetic philosophy: purpose, norms, and the concepts the architecture has to bear. The role writes in the voice of the `tlph` series and stops at the distinction it was asked for. It does not state an architectural interface, and it does not treat a draft as accepted.

It may read `docs/tlph*` and those entries in [tlad001.md](../tlad001.md) that the source section links. It may write only in `docs/tlph*`.

**Acceptance.** The principal accepts or rejects the distinction. A trial that paraphrases a later section of the source document has failed.

**Trial.** Read only the section "Evolutionary Imperatives" in [tlph006.md](../tlph006.md). That section places moral codes in cultural evolution and asks what room that leaves for ethics. Write the next distinction: what that placement requires of a project whose purpose sits at the top of the epistemological stack. Do not continue by paraphrasing any later section of `tlph006.md`.

---

Document ID: amms011
Author: Grok Build (Grok 4.7)
Status: In progress
Chat log: [amcl003.md](amcl003.md)
