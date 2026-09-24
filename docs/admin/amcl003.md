# Session record: agentic team on the DGX Spark

**Document ID**: amcl003
**Client**: Principal
**Agent**: Grok Build (Grok 4.7)
**Purpose**: Project-manager liaison on how the local team works, and on the software the DGX Spark is to carry.

The endpoint is in the documents below. This log records where each decision was placed.

| Decision | Document |
| --- | --- |
| Roles, and the rule that separates architecture from design | [amms009.md](amms009.md) |
| Order of work, including early reflexive self-improvement in HOL, the move of formal development into SPaDE repositories, and onboarding as the later main thrust | [ampl006.md](ampl006.md) |
| Local agents by default, cloud Grok and Copilot where a frontier model is warranted, Copilot review on pull requests into `main`, GitHub Issues for bounded specialist subcontracts | [ampd009.md](ampd009.md) |
| Software baseline for this Spark | [amms010.md](amms010.md) |
| ProofPower in the development container checks HOL specifications until SPaDE can. The metatheory starting point is `spc001.pp`–`spc005.pp` in the ProofPower source `src/hol`. Two local models: one writes those specifications, one uses the MCP interface (abstract syntax as JSON). ARM images are a separate line: `proofpower_arm` and `spade_arm`, built on `ubuntu-24.04-arm`. The ARM regression is manual. Pull-request regression stays on the x64 image. | [amms010.md](amms010.md), [amms009.md](amms009.md), [ampl006.md](ampl006.md) |
| First local role cards, written before a model is installed: project manager, architect, philosopher. Each card has a job, a permitted range of documents, one acceptance check, and one trial. | [amms011.md](amms011.md) |
| Roles prepare in parallel. Architecture in HOL is the urgent role. Four evaluation tasks score candidate models. ProofPower in `kr/krci001.mkf` can check scripts; the HOL4 make path cannot. A HOL fine-tune is a LoRA experiment scored by ProofPower, not part of standing up the server. | [ampl006.md](ampl006.md), [amms010.md](amms010.md) |
| The architect's first work is to recast `spc001`–`spc005` into markdown `hol` fences. ProofPower is transitional and is not a deliverable. `retro/` is outside the project standards. `common/rules.mkf` strips `hol` fences to `.sml`. `docs/tlci001.mkf` does that for `tlcd001.md`. Inference rules are to be executable, which is the first reflective self-improvement. | [amms001.md](amms001.md), [ampl006.md](ampl006.md), [amms011.md](amms011.md) |
| `retro/` is bootstrap, not SPaDE. HOL written for SPaDE in markdown is part of SPaDE. Derived documents acknowledge the ProofPower source. The SPaDE theories delete `spc005` down to `spc001` before introducing replacements. ProofPower checks well-formedness; correctness is a further check. Architectural material in `kr/` is input to new specifications in `docs/` which supersede it. The work is [amtd006.md](amtd006.md), and it waits until that description is on `main`. | [amtd006.md](amtd006.md), [amms001.md](amms001.md) |

The existing admin categories were sufficient. No `ampm` series was opened.

---

Document ID: amcl003
Author: Grok Build (Grok 4.7)
Status: In progress
