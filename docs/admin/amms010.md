# DGX Spark software baseline

This is the software the development Spark is to provide for the team in [amms009.md](amms009.md). Capabilities are the standard. A package named as a recommendation is not adopted until it is installed and recorded here as present. The order of work that drives the phasing is [ampl006.md](ampl006.md).

The machine is one NVIDIA GB10 (Grace Blackwell, `sm_121`), `aarch64`, with unified memory of about 121 GiB. Interactive development and a resident local model share that memory. Fine-tuning and focal training are scheduled so that they do not sit on top of a full-size resident model, unless the principal schedules an exception.

## Observed on this machine

Host `spark-95fb`, Ubuntu 24.04.5 LTS, kernel `7.0.0-1019-nvidia`. GPU driver 580.178.04, CUDA toolkit 13.0 (`nvcc` on the path). About 3.5 TiB free on a 3.7 TiB disk.

| Component | State |
| --- | --- |
| Git, Python 3.12, Make, CUDA toolkit | Present |
| Docker 29.6.2 and the NVIDIA container toolkit | Installed. Early development on the Spark is to use a container of the same kind as the MacBook image. The development account cannot yet run it; see below. |
| NVIDIA AI Workbench | Present under `/opt`. Not the workplace. Agents work in git worktrees. |
| GitHub CLI, Poly/ML, ProofPower, pandoc, TeX, a local model server | Absent |

## Container for early development

Early development of [SPaDE](../tlad001.md#spade) on the Spark uses a container setup like the one on the MacBook, so GitHub regression tests run in the same environment as that work.

The image is `ghcr.io/rbjones/spade:latest`, built on `ghcr.io/rbjones/pp/proofpower:latest`. ProofPower is in it because, at this stage, it is one of the two ways HOL specifications are checked, before SPaDE can check them. Documentation work does not use the container. GitHub Actions already starts the image on GitHub's runners (`runs-on: ubuntu-latest` in `.github/workflows/copilot-agent-test.yml` and `test-spade-integration.yml`).

ARM images are a separate line from the x64 images. Whether SPaDE development on the Spark runs in a container is still open. The ARM line is there so that it can.

The image-building workflow on the ProofPower fork (`rbjones/pp`, branch `utf8`) is `.github/workflows/build-container.yml`. It publishes `ghcr.io/rbjones/pp/proofpower`. `ci-container.yml` is a different job: it builds ProofPower inside `ubuntu:22.04` and does not publish an image. The ARM copy is `build-container_arm.yml`. It runs on `ubuntu-24.04-arm`, builds `linux/arm64`, and publishes `ghcr.io/rbjones/pp/proofpower_arm`.

The SPaDE ARM copy is `.github/workflows/build-spade-container_arm.yml`. It starts `FROM` `proofpower_arm:latest` and publishes `ghcr.io/rbjones/spade_arm`. The ARM regression is `.github/workflows/SPaDE_integration_arm.yml`. It runs that image on `ubuntu-24.04-arm` and is started by hand. It does not run on pull requests. The x64 workflows, including `SPaDE_integration_2.yml` on pull requests, are unchanged. `.devcontainer/devcontainer.json` still pins `linux/amd64`.

`~/git/pp` on this Spark is still `github.com/robarthan/pp`. It does not contain `build-container.yml`. The ARM ProofPower workflow is on a worktree of the fork at `~/git/pp-fork`, branch `utf8-arm`, and has not been pushed.

Running either ARM image on the Spark still needs the development account to reach the Docker daemon. That account is not in the `docker` group.

## Phase A — work the existing repository

Documentation and administration on this machine do not need the container. The ARM container line has been checked out, so this phase is no longer waiting on it.

| Capability | Requirement |
| --- | --- |
| GitHub from the shell | GitHub CLI (`gh`). Pull requests, workflow dispatch, and the issues in [ampd009.md](ampd009.md) are run from this machine. A Grok session may also reach GitHub through the GitHub MCP server. Local agents and an ordinary shell do not. `gh` is not installed yet. The ARM container line has been checked out, so this install is no longer waiting on that. |
| Python development | A virtual environment with the packages in the repository `requirements.txt` (`flake8`, `mypy`, `pytest`, `mcp`, `fastmcp`, `cryptography`, `yamllint`). |
| Document build | `pandoc` and `pdflatex`, when a document build that needs them is actually run (`docs/tlci001.mkf`). |
| Native C/C++ build | A compiler and CMake, before a `llama.cpp` build. The CUDA toolkit is already present. |

## Local models for the first roles

The first roles are briefed in [amms011.md](amms011.md). Architectural evaluation is the urgent use, and it is specified in [ampl006.md](ampl006.md). One native OpenAI-compatible server serves every model: `llama.cpp` built for this GPU (`sm_121`) and exposed through `llama-server`, as in NVIDIA's DGX Spark playbooks. The weights are GGUF. Containerised servers remain a later alternative.

Two selections of weights, not two servers. Only one heavy model is resident during a task.

| Selection | Use | Size class |
| --- | --- | --- |
| Large instruct model | Architect and philosopher trials. One model, two document packs. | About 70 billion parameters, quantised so that a long context still fits in the 121 GiB unified memory. |
| Smaller instruct model | Project-management drafting against a written procedure. | About 30 billion parameters. |

The exact weights are chosen at install by running the architect's read task and the project-manager trial, and keeping the model that ProofPower, or the principal, accepts. They are not chosen from a catalogue in advance.

## Assessing a HOL fine-tune

A fine-tune is an experiment against the hold-out tasks in [ampl006.md](ampl006.md) (write, and repair). It is not installed as part of standing up the server.

The scorer is ProofPower, in `ghcr.io/rbjones/pp/proofpower_arm`. A script counts as a success when that image accepts it. Prose quality is not the score.

The comparison is one smaller base model against a LoRA of that same base. The training corpus is the ProofPower `spc` series and HOL scripts this repository already runs through ProofPower, excluding the hold-out tasks. The large architect model is not the model that is fine-tuned in this experiment. If the LoRA changes the acceptance rate on the hold-out, tuning matters for reading and writing HOL, and a specialist can be paired with the large model. If it does not, the large model remains the architect alone.

The trainer is installed only for that experiment. NVIDIA's Spark playbooks include Unsloth and LLaMA-Factory. The one that is used has to have been shown to run on `sm_121`. Official PyTorch wheels may warn on that architecture.

## Later model kinds

Two further kinds of model come after the first roles. They use the same server. Only one heavy model is resident during a task.

| Kind | Job |
| --- | --- |
| Specification model | Writes formal specifications of SPaDE and its subsystems while the first prototypes are being developed. At this stage those specifications are checked in the ProofPower container. The architectural trial is the first use of this kind. |
| MCP model | Talks to SPaDE through the MCP interface, in abstract syntax as JSON, and carries the theory hierarchy forward inside SPaDE repositories. SPaDE does not take concrete syntax. |

An agent harness, beyond the cloud sessions already in use, is installed when a local role is ready to be staffed. The requirement is a harness that takes a local OpenAI-compatible endpoint, works in a git worktree, and can be given a role. No harness is selected in this baseline.

## Deferred

Focal training stays uninstalled until layered [perfect information spaces](../tlad001.md#perfect-information-space) are ready to run continuously. A single-Spark pretraining stack is out of scope. Node is not required by the repository as it stands.

---

Document ID: amms010
Author: Grok Build (Grok 4.7)
Status: In progress
Chat log: [amcl003.md](amcl003.md)
