# DGX Spark software baseline

This document records the observed software baseline and the next planned capabilities for the development Spark described in [amms009.md](amms009.md). A recommendation is not an adopted capability until it is installed and verified here. As planned work is completed, update the plan to record the resulting state. The order of work is in [ampl006.md](ampl006.md).

The machine is one NVIDIA GB10 (Grace Blackwell, `sm_121`), `aarch64`, with unified memory of about 121 GiB. Interactive development and a resident local model share that memory. Fine-tuning and focal training are scheduled so that they do not sit on top of a full-size resident model, unless the principal schedules an exception.

## Observed on this machine

Host `spark-95fb`, Ubuntu 24.04.5 LTS, kernel `7.0.0-1019-nvidia`. GPU driver 580.178.04, CUDA toolkit 13.0 (`nvcc` on the path). About 3.5 TiB free on a 3.7 TiB disk.

| Component | State |
| --- | --- |
| Git, Python 3.12, Make, CUDA toolkit | Present |
| Docker 29.6.2 and NVIDIA Container Toolkit 1.20.0 | Present. GPU access has been verified in CUDA and vLLM containers. |
| Ollama 0.34.4 | Installed as a user service. Its current ARM64 distribution uses CPU inference on the GB10. |
| vLLM and `Qwen/Qwen3-32B-AWQ` | GPU inference verified in the ARM64 container; the local API is `local-llm`. |
| NVIDIA AI Workbench | Present under `/opt`. Not the workplace. Agents work in git worktrees. |
| GitHub CLI, Poly/ML, ProofPower, pandoc, TeX | Not part of the verified LLM stack; see the repository development requirements below. |

## Container for early development

Early development of [SPaDE](../tlad001.md#spade) on the Spark uses a container setup like the one on the MacBook, so GitHub regression tests run in the same environment as that work.

The image is `ghcr.io/rbjones/spade:latest`, built on `ghcr.io/rbjones/pp/proofpower:latest`. ProofPower is in it because, at this stage, it is one of the two ways HOL specifications are checked, before SPaDE can check them. Documentation work does not use the container. GitHub Actions already starts the image on GitHub's runners (`runs-on: ubuntu-latest` in `.github/workflows/copilot-agent-test.yml` and `test-spade-integration.yml`).

ARM images are a separate line from the x64 images. Whether SPaDE development on the Spark runs in a container is still open. The ARM line is there so that it can.

The image-building workflow on the ProofPower fork (`rbjones/pp`, branch `utf8`) is `.github/workflows/build-container.yml`. It publishes `ghcr.io/rbjones/pp/proofpower`. `ci-container.yml` is a different job: it builds ProofPower inside `ubuntu:22.04` and does not publish an image. The ARM copy is `build-container_arm.yml`. It runs on `ubuntu-24.04-arm`, builds `linux/arm64`, and publishes `ghcr.io/rbjones/pp/proofpower_arm`.

The SPaDE ARM copy is `.github/workflows/build-spade-container_arm.yml`. It starts `FROM` `proofpower_arm:latest` and publishes `ghcr.io/rbjones/spade_arm`. The ARM regression is `.github/workflows/SPaDE_integration_arm.yml`. It runs that image on `ubuntu-24.04-arm` and is started by hand. It does not run on pull requests. The x64 workflows, including `SPaDE_integration_2.yml` on pull requests, are unchanged. `.devcontainer/devcontainer.json` still pins `linux/amd64`.

`~/git/pp` on this Spark is still `github.com/robarthan/pp`. It does not contain `build-container.yml`. The ARM ProofPower workflow is on a worktree of the fork at `~/git/pp-fork`, branch `utf8-arm`, and has not been pushed.

The verified GPU-container access does not imply that SPaDE development itself has moved into a container. Documentation work does not use the container, and the development-container workflow remains a separate decision.

## Phase A — work the existing repository

Documentation and administration on this machine do not need the container. The ARM container line has been checked out, so this phase is no longer waiting on it.

| Capability | Requirement |
| --- | --- |
| GitHub from the shell | GitHub CLI (`gh`). Pull requests, workflow dispatch, and the issues in [ampd009.md](ampd009.md) are run from this machine. A Grok session may also reach GitHub through the GitHub MCP server. Local agents and an ordinary shell do not. `gh` is not installed yet. The ARM container line has been checked out, so this install is no longer waiting on that. |
| Python development | A virtual environment with the packages in the repository `requirements.txt` (`flake8`, `mypy`, `pytest`, `mcp`, `fastmcp`, `cryptography`, `yamllint`). |
| Document build | `pandoc` and `pdflatex`, when a document build that needs them is actually run (`docs/tlci001.mkf`). |
| Native C/C++ build | A compiler and CMake are needed only if a native project build is required. The local GPU model server uses vLLM rather than the previously planned `llama.cpp` build. |

## Local model service

The initial plan was to use `llama.cpp` and `llama-server`, following NVIDIA's DGX Spark playbooks. In this setup, `llama.cpp` did not provide GPU inference on the GB10, so the plan changed to vLLM. This records the result on this machine, not a general claim about every `llama.cpp` build.

The Docker Compose `serve` profile runs the ARM64 vLLM image pinned in the local stack configuration. It has been verified with PyTorch 2.13.0, CUDA 13.0, and the GB10 (`sm_121`). The configured model is `Qwen/Qwen3-32B-AWQ`, exposed as `local-llm`; its checkpoint is approximately 18 GiB. The endpoint listens only on `127.0.0.1:8000` and has no authentication, so it must not be exposed directly to a network.

Start or recreate the service:

```sh
cd ~/.local/share/llm-stack
docker compose --profile serve up -d
```

Inspect or stop it:

```sh
curl http://127.0.0.1:8000/v1/models
docker compose --profile serve logs -f vllm
docker compose --profile serve down
```

Ollama remains available for its local API and model-management interface, but its current ARM64 distribution does not support CUDA on this GPU and therefore uses CPU inference. GPU inference is provided by vLLM. Only one heavy model should be resident when GPU memory is needed for other work.

## Local agent harness

OpenHands is the preferred next option for open-ended local design and coding tasks. It provides a browser interface and runs the agent's shell, tools, and repository operations in a Docker sandbox. It is complementary to interactive use of Grok Build or Copilot CLI.

OpenHands can use the vLLM API as an OpenAI-compatible provider with model `openai/local-llm`, base URL `http://127.0.0.1:8000/v1`, and a non-empty local placeholder API key unless authentication is added. Its container must use Docker host networking for this loopback URL to work. Do not expose unauthenticated vLLM on a network interface; use an authenticated, access-controlled proxy if host networking is unsuitable.

Mount only the repository needed for a task, and grant write access only when intended. State each task's outcome and validation, inspect its diff, and run the project checks before accepting changes. Before replacing the current model, validate a representative agent task that reads files, makes a small change, runs a command, and returns a reviewable diff. Configure Qwen's chat template and non-thinking/tool-use settings, and retain at least the current 32k context window.

## Assessing a HOL fine-tune

The `tune` Compose profile defines a separate image based on the verified ARM64 vLLM image, with `accelerate`, `datasets`, `peft`, and `trl`. Build it only when tuning work is to begin. Put datasets in `~/.local/share/llm-stack/data/` and outputs in `~/.local/share/llm-stack/output/`.

```sh
cd ~/.local/share/llm-stack
docker compose --profile tune build tune
docker compose --profile tune run --rm tune
```

A fine-tune remains an experiment against the hold-out tasks in [ampl006.md](ampl006.md) (write and repair), not part of standing up the server. The scorer is ProofPower in `ghcr.io/rbjones/pp/proofpower_arm`; a script succeeds when that image accepts it. Compare one smaller base model with a LoRA of the same base, using the ProofPower `spc` series and repository HOL scripts for training while excluding hold-out tasks. LoRA or QLoRA is the single-GPU default for 70B-class models; full-parameter training is not.

The tuning profile has not yet been built or evaluated. Before selecting another trainer or updating the pinned vLLM image, verify GPU support on `sm_121` and run a completion request. Official PyTorch wheels may warn on that architecture.

## Later model kinds

Two further kinds of model come after the first roles. They use the same server. Only one heavy model is resident during a task.

| Kind | Job |
| --- | --- |
| Specification model | Writes formal specifications of SPaDE and its subsystems while the first prototypes are being developed. At this stage those specifications are checked in the ProofPower container. The architectural trial is the first use of this kind. |
| MCP model | Talks to SPaDE through the MCP interface, in abstract syntax as JSON, and carries the theory hierarchy forward inside SPaDE repositories. SPaDE does not take concrete syntax. |

OpenHands is the preferred harness for initial local trials. Later role-specific harnesses can be evaluated when the specification and MCP model roles are ready to be staffed.

## Deferred

Focal training stays uninstalled until layered [perfect information spaces](../tlad001.md#perfect-information-space) are ready to run continuously. A single-Spark pretraining stack is out of scope. Node is not required by the repository as it stands.

## Configuration and maintenance

The local stack configuration is in `~/.local/share/llm-stack/`; user data, datasets, and generated output remain outside the SPaDE worktree. Copy `.env.example` to `.env` before changing the model, port, context length, or GPU memory allocation. Keep `.env` permissions restricted, and provide any Hugging Face token locally rather than adding it to the repository.

The vLLM image is pinned by digest. Before changing that digest, rerun the GPU probe and a completion request to confirm GB10 support. The complete local-stack usage notes are maintained in `~/.local/share/llm-stack/README.md`.

---

Document ID: amms010
Primary authors: Grok Build (Grok 4.7); GitHub Copilot CLI (GPT-5.6 Terra)
Status: In progress
Chat log: [amcl003.md](amcl003.md)
