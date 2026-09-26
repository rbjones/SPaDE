# Development on the DGX Spark

Roles and placement are in [amms009.md](amms009.md). The software the Spark is to carry is in [amms010.md](amms010.md). How a task is given out is in [ampd009.md](ampd009.md).

The workplace for development is this DGX Spark. Cloud models are reserved for the cases in [ampd009.md](ampd009.md).

## Parallel preparation

The roles work at the same time. A dependency is a constraint on what a role may treat as settled, not a reason for the role to wait. The most urgent role to staff is architectural design and its formalisation in HOL. The first local role cards are in [amms011.md](amms011.md). The software for running and comparing local models is in [amms010.md](amms010.md).

| Role | Can proceed now | Depends on another role for |
| --- | --- | --- |
| Architect | Write the generic theory of abstract syntax in [amtd006.md](amtd006.md). `spc001`–`spc005` are reference only. Evaluate candidate models only after that task description is on `main`. | A new philosophical distinction, only once a specification depends on a concept the principal has not accepted. |
| Philosopher | Distinctions in `docs/tlph*`, including the trial in [amms011.md](amms011.md). | Nothing, to draft. The principal accepts or rejects. |
| Project manager | Role cards, the software baseline, occupancy, and the text of specialist issues. | An agreed paragraph for each document. |
| Subsystem design, implementation, and test | Separate architectural interfaces from detailed design in the existing subsystem documents, and list what would be promoted to `tlad`. | The HOL specification of an interface, before building to it. |
| Knowledge onboarding | Catalogue the theories already in `retro/` and in the ProofPower `spc` series, as a corpus. | [SPaDE](../tlad001.md#spade) repositories, before autoformalising into them. |
| Focal trainer | Read the account of perfect-information spaces. | Those spaces, before any training run. |

## Architectural evaluation

These tasks can be run before a model is chosen as the architect. The write and repair tasks are the hold-out set for the tuning comparison in [amms010.md](amms010.md).

1. **Read.** From the opening of `spc001.pp`, state the HOL language fragment it defines. Score by agreement with that document.
2. **Place.** In the section "Abstract Models of the Knowledge Repository" of [tlad012.md](../tlad012.md), mark which names are architectural interfaces under the rule in [amms009.md](amms009.md).
3. **Write.** The architect trial in [amms011.md](amms011.md): HOL for the distinction between a context and a view. ProofPower must accept the script.
4. **Repair.** Given a small script derived from a theory ProofPower already accepts, with one introduced fault, return a script ProofPower accepts.

## Checking HOL

Until [SPaDE](../tlad001.md#spade) can check HOL specifications, ProofPower does. The starting point for the metatheory is `spc001.pp`–`spc005.pp` in the ProofPower source `src/hol`. The series is not exactly the HOL metatheory SPaDE needs. An early target remains a version of that theory in a SPaDE repository. Copies of `spc001.pp` and `spc003.pp` also sit in `retro/np/`.

SPaDE does not take concrete syntax. It takes abstract syntax as JSON through the MCP interface. That interface is a later path. The specifications written now are ProofPower HOL inside markdown (`hol` fences), stripped to `.sml` by `common/rules.mkf`. Each theory a specification creates is opened with `force_delete_theory`, so a rebuild re-checks that specification and those that depend on it. The first of them is a generic abstract syntax, [amtd006.md](amtd006.md), not a transcription of `spc001`–`spc005`. The deductive system remains that of the `spc` series, expressed so that it is constructive and executable. ProofPower checks well-formedness until SPaDE can. It is not part of the deliverable. Specifications already under `kr/` in HOL4 stay where they are. New architectural HOL does not use HOL4.

The ProofPower path in `kr/krci001.mkf` and `common/rules.mkf` does run scripts through ProofPower. [SPaDE Integration Test (ARM) #4](https://github.com/rbjones/SPaDE/actions/runs/35878870587) ran `make` to completion in `ghcr.io/rbjones/spade_arm`, which builds the `maths_egs` and `rbjhol` databases, loads the `spc` series, and compiles the ProofPower SML under `kr/`. On this Spark, `pp` is not installed and `PPDIR` is unset, so that path is the container's, not a native one.

That makefile is not yet a runner for a new architectural script. A candidate `.pp` file is checked only after `ppsml` has made an `.sml` and the file has been added to the load list. `dk/Makefile` is aimed at the `spc` series itself: it copies `spc001.pp`–`spc005.pp` from `~/git/pp/src/hol` and compiles them in order into a database `dkdb` whose parent is `hol`. The parent database is assumed to exist. Its document rules are unfinished (`pandoc yourfile.md`, and `PDFFILES` is never defined). It is not the makefile the regression runs.

The HOL4 path is not ready. `common/rules.mkf` defines `HOL4LDD` and a recipe that calls `hol`, but `kr/krci001.mkf` gives `$(SPADEHOL4DBNAME).ldd` an empty recipe, and that name is `spade`, the same stamp as the ProofPower database. `check` depends on `$(H4LDD)`, which is never set, so the passing regression did not run HOL4. `kr/krcd006.sml` is HOL4 script (`app load`, `Datatype:`), and HOL4 is not in the container. ProofPower is the checker for the architectural trial. HOL4 is a second checker after it has its own heap and its own make target.

## Later endpoints

These remain the endpoints. They are not a queue.

1. **Reflexive self-improvement.** The specifications it depends on are fully formal in HOL, so they can enter [SPaDE](../tlad001.md#spade) logical contexts and yield SPaDE metatheory.
2. **Formal development in the git repository.** Until SPaDE repositories can hold it, formal work stays here. Whether Spark development runs in the container is still open. The ARM images `proofpower_arm` and `spade_arm` exist. Pull-request regression stays on the x64 image. Documentation does not use a container.
3. **Move the formal development** into SPaDE repositories.
4. **Knowledge onboarding** becomes the main thrust after that move.
5. **Focal training** runs continuously once layered [perfect information spaces](../tlad001.md#perfect-information-space) are ready.

Narrative, philosophy, architecture, administration, and the host software remain in the git repository. The architect maintains top-level strategy in the `ampl` series, with the principal's support, and technical strategy that states architectural interfaces in the `tlad` series.

The subsystem sequence sketched in [ampl005.md](ampl005.md) stands until the architect replaces it. [ampl001.md](ampl001.md) and [ampl004.md](ampl004.md) remain the longer accounts.

---

Document ID: ampl006
Author: Grok Build (Grok 4.7)
Status: In progress
Chat log: [amcl003.md](amcl003.md)
