# Continuous ProofPower HOL LLM Training Research Plan

This plan turns the preliminary fine-tuning proposal in
[ampl007.md](ampl007.md) into a continuing experimental programme. Its first
purpose is to determine how far a local model on the DGX Spark can assist with
ProofPower HOL specifications and proofs. Its later purpose is to apply the
same evidence-led method to models which mediate between human users and the
SPaDE MCP server, and eventually to the supervision and training of focal
intelligence.

The programme begins with ProofPower only. HOL4, HOL Light, and Isabelle/HOL
are possible later comparison corpora, not sources for the first adapter.
The first experimental priority is ProofPower specification and proof work,
rather than a tune for the still-changing MCP interface.

## Principles

1. **Evaluation before tuning.** A base model is tested against fixed,
   unseen tasks before a training run is commissioned. A tune is justified by
   a measured deficiency, not by the availability of a corpus.
2. **The prover is the judge.** ProofPower acceptance is the primary
   correctness signal for a script, proof step, or completed proof. It does
   not establish that the generated specification expresses the intended
   requirement; that remains an architectural and human judgement.
3. **Provenance and separation.** Each example records its source revision,
   extraction method, and task class. Held-out tests and their dependencies
   are excluded from training. No result is accepted without enough
   information to reproduce it.
4. **Separate capabilities.** Specification/proof and MCP-use adapters are
   separately trained and evaluated, even if they share a base model. This
   avoids treating tool use, JSON construction, and ProofPower concrete syntax
   as one unmeasured skill.
5. **Small reversible changes.** Begin with a LoRA or QLoRA adapter on a
   model that already has adequate code, mathematical, and tool-use ability.
   Keep the base checkpoint immutable and retain every adapter separately.
6. **Continuous review.** Each completed phase supplies evidence for the
   next decision. The programme is supported by detailed discussion of the
   ProofPower materials and capabilities; it is not an unattended training
   pipeline at this stage.

## Phase 0 -- establish the training environment

The existing `tune` Docker Compose profile is the first installation path. It
is based on the ARM64 vLLM image already verified on the GB10 and specifies
`transformers`, `peft`, `trl`, `datasets`, and `accelerate`. Before a real
run:

1. Build the `tune` profile, with datasets and outputs outside the SPaDE
   worktree as specified in [amms010.md](amms010.md).
2. Stop the resident vLLM model. A tuning run and a full-size serving model do
   not share the Spark's unified memory.
3. Record the image digest, GPU driver, CUDA, PyTorch, Python, package
   versions, model revision, and relevant training configuration.
4. Run a GPU-visible import, a small forward pass, and a tiny LoRA training
   step. Do not select a trainer from a claimed feature list alone: confirm
   that it runs on `sm_121`.
5. If that path fails, assess LLaMA-Factory and then Unsloth as alternatives,
   with the same smoke checks. Do not replace the pinned serving image until
   GPU inference and a completion have been reverified.

The practical first candidate model is a smaller instruction-following,
code-and-mathematics-capable model which can be trained and interact with
ProofPower promptly. The current Qwen checkpoint is a natural first
comparison candidate. GPT-OSS and Qwen3.6 remain important serving and
baseline candidates, but their size makes them less suitable for the first
interactive training experiment. Model choice is made from measured baseline
results, licensing, context capacity, and successful Spark training support,
not solely parameter count.

## Phase 1 -- inventory and preserve the ProofPower evidence

Create a versioned manifest of the selected ProofPower checkout before
extracting examples. The manifest identifies the repository URL, commit,
branch, applicable licence, build command, files included, and any generated
artefacts. Retain the raw source and build output unchanged; derived datasets
are additional, reproducible artefacts.

The initial inventory distinguishes:

| Evidence | First use | Limitation |
| --- | --- | --- |
| Literate `.pp` sources, especially `src/hol` and `spc001.pp`--`spc005.pp` | Syntax, specification paragraphs, tactic vocabulary, and completed proof structure | Successful text alone does not expose failed search or intermediate states |
| `zed` and `daz` proof sources | Additional tactic and proof examples under semantic embeddings | They are not examples of SPaDE's HOL specification notation |
| Full build logs | Confirmation that a source revision builds and a source of theorem/proof boundaries | Logs must be associated with exact source and build environment; they may be verbose and nondeterministic |
| Interactive ProofPower sessions | State-action-result trajectories, including failed tactics and changed goal stacks | Requires a controlled harness and a fresh theory/database for each trial |
| SPaDE specifications in this repository | The target dialect, intended architecture, and small held-out requirements | They must never be silently mixed into training and evaluation sets |

Build logs are valuable, but they are not automatically training data. First
determine whether they identify commands, goals, tactics, and outcomes
reliably enough to align them with their source. A log which cannot be
attributed to a source theorem is retained as provenance, not converted into a
supervised example.

## Phase 2 -- define baselines and held-out tasks

Before creating an adapter, evaluate each candidate base model under recorded,
fixed prompts and tool settings. The starting suite is the architectural
evaluation in [ampl006.md](ampl006.md):

1. explain the HOL language fragment from the opening of `spc001.pp`;
2. identify architectural interfaces in `tlad012.md`;
3. write the context-and-view specification and check it in ProofPower; and
4. repair a deliberately faulted, otherwise accepted script.

Extend the suite only with tasks whose sources and dependencies are excluded
from the training set. Report at least: ProofPower acceptance rate, proof-step
acceptance rate, completion rate within a fixed attempt budget, repair rate,
and human assessment of whether accepted specifications meet their stated
requirements. Preserve failed as well as successful outputs.

The result of this phase is a capability map: what a base model already does,
what it cannot do, and whether the shortfall is primarily syntax, theorem
selection, tactic search, context management, or architectural
understanding. Only a repeatable gap justifies training.

## Phase 3 -- construct versioned datasets

Dataset construction is a separate engineering task, not a side effect of a
trainer. It produces machine-readable records with at least:

- source repository and immutable revision;
- source file and stable source span;
- ProofPower context or parent theory;
- task kind (`explanation`, `specification`, `proof`, `repair`, or
  `interactive-step`);
- input, expected or observed output, and checker result;
- extraction-program revision; and
- split assignment and the reason it is held out.

Create the following datasets in order:

1. **Read and explain.** Instruction-answer examples grounded in selected
   ProofPower sources and manuals. These test understanding but do not claim
   formal correctness.
2. **Completed scripts.** Source-derived, structurally bounded
   specification/proof examples. Preserve the surrounding theory context
   required for a script to be meaningful.
3. **Repair pairs.** Accepted scripts with controlled, documented faults and
   the original accepted version as the target. Generate these only when the
   fault and repair are independently checked.
4. **Interactive trajectories.** Goal, context, proposed tactic, resulting
   goal stack or explicit ProofPower failure. These are collected through a
   harness, not inferred from prose logs.

Use source-family or theory-level splitting, rather than a random line-level
split, wherever possible. Near-duplicate theorem or tactic sequences in train
and test would make proof performance appear better than generalisation.

## Phase 4 -- run the first supervised adapter experiment

Once Phase 2 identifies a measurable gap and Phase 3 yields a reviewed
dataset, train a small LoRA/QLoRA adapter. Start with one task class and a
small parameter/configuration sweep rather than combining every source and
objective. Compare the adapter with the exact base model on:

- the held-out suite;
- the relevant ProofPower checker results;
- representative general coding and mathematical prompts used as regression
  checks; and
- generation cost, run time, and Spark memory use.

The adapter advances only if it improves the intended held-out measure without
an unacceptable regression. Keep the training configuration, random seeds
where available, checkpoints, and evaluation reports. A non-improving run is
also a result: retain it and revise the data or hypothesis before repeating.

## Phase 5 -- introduce verifier-guided proof exploration

Supervised examples teach notation and the shape of prior successful work.
They do not by themselves teach search through a new proof state. After a
useful supervised baseline exists, implement a small interactive ProofPower
harness which:

1. creates or restores an isolated, declared theory context;
2. presents a goal and permitted proof context to the model;
3. submits one proposed tactic or bounded tactic sequence;
4. returns the resulting goal stack or an explicit error; and
5. records the full trajectory with the checker outcome.

Begin with bounded, reproducible exercises and a smaller model so that the
CPU checker and GPU generation remain practical. Use accepted and failed
steps as training and analysis evidence only after checking that the task
statement and context are sound. Any reinforcement- or preference-style
training comes after this harness produces stable, interpretable trajectories;
it is not the first tuning method.

## Phase 6 -- later MCP and SPaDE training streams

As the MCP server develops, record accepted and rejected tool calls against
versioned server contracts. Each record includes the tool schema, server
revision, request, response, repository state, and round-trip or semantic
validation result. Do not train an MCP adapter until repeated, measured
tool-use failures remain after prompt and tool-description improvements.

When formal specifications and proofs migrate from Git into SPaDE repositories,
that migration becomes another separately evaluated task. The source
specification, target abstract syntax, MCP interaction trace, SPaDE
validation, and any error must be retained together. SPaDE's validation will
then provide a second ground-truth signal, distinct from ProofPower's
concrete-syntax and proof-checking signal.

Focal-intelligence training remains a later programme. It begins only when
layered perfect-information spaces are available to generate stable state,
action, and outcome data. The work above prepares useful methods for
provenance, evaluation, and verifier-guided learning, but does not assume
that a general LLM adapter is itself focal intelligence.

## Experiment record and review rhythm

Every experiment has a short, version-controlled record containing its
question, hypothesis, model and dataset identifiers, complete environment,
commands/configuration, resource use, held-out results, samples of failures,
and decision. Store raw datasets, build logs, model weights, and large
generated outputs outside the SPaDE worktree in the locations specified by
[amms010.md](amms010.md); store manifests, extraction code, configurations,
and concise reports in version control.

The immediate next decision is whether the prepared `tune` profile can make a
verified small LoRA step on the Spark. That installation check is followed by
the ProofPower inventory and the frozen baseline suite. Results are reviewed
in discussion before commissioning dataset construction, an adapter run, or
the interactive harness.

---

Document ID: ampl008  
Author: GitHub Copilot CLI (GPT-5.6 Terra)  
Status: Draft
