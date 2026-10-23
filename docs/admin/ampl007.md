# Fine-tuning for specifications and the MCP interface

Evaluating existing models for writing HOL specifications, and moving the knowledge repository forward, comes before any tuning run. This note records the software available for a run on the Spark, and a preliminary recommendation for two tunes: writing ProofPower HOL specifications, including some proof, and using the [SPaDE](../tlad001.md#spade) MCP interface. A run is commissioned only after a trial of an existing model has shown a gap. The machine facts for the prepared training profile are in [amms010.md](amms010.md). The hold-out tasks are the write and repair tasks in [ampl006.md](ampl006.md).

## What a fine-tune changes

Fine-tuning continues the training of a model that already follows instructions, on examples of one kind of work. The weights change. A prompt leaves them as they are.

The work has seven parts.

1. Name the change, and the held-out test that will show whether it happened.
2. Choose a base model that is already close to the work.
3. Build examples in the format that base model was trained to read.
4. Choose how much of the model moves. LoRA trains small adapter matrices and leaves the base weights frozen. QLoRA does the same while the frozen base is held in a reduced precision. Full fine-tuning updates every weight.
5. Choose the objective. Supervised training shows completed examples. Preference training shows a better answer beside a worse one. Reinforcement learning with a checker scores each attempt.
6. Train, then repeat tasks the base model already did well, to see whether the new skill displaced them.
7. Export the adapter, merged or kept separate, and serve it in place of the base. On this Spark the serving path is the vLLM service in [amms010.md](amms010.md). The resident model is stopped first. The machine has one GB10 and about 121 GiB of unified memory.

LoRA or QLoRA is the practical default at 70B scale. Full updates fit more easily around 30B and below. The GB10's memory bandwidth makes a run slower than a datacentre GPU of the same generation. One heavy model is resident at a time. A tuning run is scheduled so that it does not sit on top of the full-size resident model.

## Software

Three trainers match this machine. None of them is installed. Official PyTorch wheels may warn on `sm_121`, so a run starts from an environment already shown to see the GB10, then a completion, then a tiny training step.

| Trainer | What it covers | On this Spark |
| --- | --- | --- |
| Hugging Face `transformers`, `peft`, `trl`, `datasets`, `accelerate` | Supervised, preference, and checker-scored training; LoRA and QLoRA | The `tune` Compose profile in [amms010.md](amms010.md) is this stack on the verified ARM64 vLLM image. It is specified and has not been built. Datasets go in `~/.local/share/llm-stack/data/` and outputs in `~/.local/share/llm-stack/output/`. |
| LLaMA-Factory | The same methods behind one command-line interface and example configurations | NVIDIA's DGX Spark playbook, updated 14 October 2026, uses PyTorch for CUDA 13.0 and demonstrates Qwen3 LoRA. |
| Unsloth | Faster, lower-memory LoRA and QLoRA, reinforcement learning, and export to Hugging Face, vLLM, and GGUF | NVIDIA's Spark playbook runs it in the PyTorch container. It needs kernels built for the GB10. |
| NVIDIA Transformer Engine | NVFP4 and MXFP8, the reduced precisions this Blackwell chip provides | A further option when a reduced-precision LoRA is wanted in a form native to the GPU. |

The first run uses the `tune` profile, because it is already specified on the image that has been shown to serve on this GPU. LLaMA-Factory or Unsloth is the alternative if that profile cannot train on `sm_121`. The examples and the held-out test are the long part of the work. The trainer is a short program once those exist.

## Writing specifications

The urgent tune is a model that writes ProofPower HOL, and that carries out some of the proof in that dialect. The specification it writes is a literate script. The prose states the requirement and can be read on its own. The HOL formalises that prose. ProofPower accepts a proof relative to the goal that was set. Acceptance of a specification means the script is well-formed and its proofs go through. The prose remains the statement of what was to be formalised. The method for the scripts is [amms012.md](amms012.md).

The ProofPower build at `~/git/pp` is the corpus. In order it builds `pptex`, `dev`, `hol`, `zed`, and `daz`: about 520 literate `.pp` documents, about 15 MB. The HOL database teaches the specification notation and the proofs conducted in that context. That package is 240 documents, about 7 MB, with 770 `set_goal` calls and 342 `save_pop_thm` calls. A stored proof is `set_goal`, one or more `a(tactic)` steps, and `save_pop_thm`. Those files are the successful scripts.

The `zed` and `daz` proofs belong in the proof corpus. They are proofs in the same deductive system, with the same SML subgoal package, in the extra context of a semantic embedding. `src/zed/usr011D.pp` uses `set_goal` and `a(tactic)`, and the `zed` documents contain 478 `set_goal` calls. `src/daz/mdt530.pp` sets goals from conjectures and discharges them the same way. Those documents teach proof under an embedding. They do not add examples of the HOL specification notation.

HOL4 and HOL Light are further sources of the same logic, with larger libraries and a different presentation. Which is easier to draw on is open. HOL4 is SML, and some of its scripts are already under `kr/`. It is not installed on this Spark, so it cannot yet judge a script here. HOL Light is OCaml, and its proofs often sit closer to the primitive inferences. Either corpus can teach proof structure. A model that emits ProofPower tactics still has ProofPower as the judge. The cost is in using the foreign scripts as they stand, or in translating them into ProofPower's notation.

Training has two passes. Supervised training on the successful scripts teaches the notation, the tactic vocabulary, and the shape of a finished specification or proof. The corpus is small: enough to move a model that already writes code or formal mathematics, and thin as the only teaching signal. The interactive pass gives ProofPower a goal, takes a proposed step from the model, and returns the new goal stack or a refusal. Accepted steps that finish at `save_pop_thm` are proofs of the statement that was set. Refusals and stuck stacks are teaching signal as well. The stored scripts say which theorems are reachable. The live tool supplies the attempts.

The harness for that loop is the piece still to be written. It opens a theory database, passes a goal and a tactic, and returns the goal stack or the error. The build already drives ProofPower in batch, and the loop is a step-by-step use of that interface. ProofPower is CPU work beside the GPU. The first loops use a smaller base model, so each tactic comes back quickly.

The write and repair tasks in [ampl006.md](ampl006.md) are the held-out test. Reproducing the build is not evidence that the model can write a theory it did not train on.

The preliminary recommendation is to score existing models on those tasks before any adapter is trained. If a gap remains, train one LoRA of a smaller base. The specification notation comes from the HOL database documents. The proof examples come from `hol`, `zed`, and `daz`. The hold-out tasks stay out of the training set. The interactive loop follows that supervised pass. HOL4 and HOL Light stay undecided until a sample of each has been compared with ProofPower's notation.

## Using the MCP interface

The second tune talks to [SPaDE](../tlad001.md#spade) through the MCP server and carries a theory hierarchy forward inside a SPaDE repository. The server takes abstract syntax as JSON. It does not take concrete syntax. The current server, `mcp/mcpcd001.py`, offers three tools: `create_repository`, `write_sexpression`, and `read_sexpression`. A written expression is a JSON value whose strings become atoms, whose lists become cons chains, and whose null becomes nil. The server returns success with a sequence number, or an error string. `mcp/mcpte001.py` exercises that path. It is a test, not a body of examples.

The judge is the server. A call that writes an expression and reads the same expression back has succeeded. A call that the server rejects, or that reads back something other than what was written, has failed. There is not yet a corpus of such dialogues. The interface is still the prototype, and examples collected against it would be discarded as the repository operations grow.

The preliminary recommendation is to leave this adapter untrained while the knowledge repository's specification and implementation move forward. As those operations settle, keep the accepted and rejected calls. Try an existing tool-using model against the live server before commissioning a tune. When the same failures repeat, train one LoRA, separate from the specification adapter. The two adapters can share a base model. This one emits abstract syntax as JSON. The specification adapter emits ProofPower HOL.

## Code from a specification

Generating Python from a specification is not one of these two tunes. The Python now in the repository was produced by existing models from informal specifications. A literate specification gives such a model the prose of the requirement and the HOL that formalises it. The first use is to ask for the Python with both in hand. A tune for that translation waits until a trial shows that this is not enough. Where the HOL is constructive, the same cases can be run on both sides, and that comparison is the judge.

---

Document ID: ampl007
Author: Grok Build (Grok 4.7)
Status: In progress
