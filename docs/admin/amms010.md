# DGX Spark software baseline

This document records the observed software baseline and the next planned capabilities for the development Spark described in [amms009.md](amms009.md). Capabilities are the standard; a recommendation is not an adopted capability until it is installed and verified here. As planned work is completed, update the plan to record the resulting state. The order of work is in [ampl006.md](ampl006.md).

The machine is one NVIDIA GB10 (Grace Blackwell, `sm_121`), `aarch64`, with unified memory of about 121 GiB. Interactive development and a resident local model share that memory. Fine-tuning and focal training are scheduled so that they do not sit on top of a full-size resident model, unless the principal schedules an exception.

## Observed on this machine

Host `spark-95fb`, Ubuntu 24.04.5 LTS, kernel `7.0.0-1019-nvidia`. GPU driver 580.178.04, CUDA toolkit 13.0 (`nvcc` on the path). About 3.5 TiB free on a 3.7 TiB disk.

| Component | State |
| --- | --- |
| Git, Python 3.12, Make, CUDA toolkit | Present |
| Docker 29.6.2 and NVIDIA Container Toolkit 1.20.0 | Present. GPU access has been verified in CUDA and vLLM containers. |
| Ollama 0.34.4 | Installed as a user service. Its current ARM64 distribution uses CPU inference on the GB10. |
| vLLM and `Qwen/Qwen3-32B-AWQ` | GPU inference verified in the ARM64 container; the local API is `local-llm`. |
| OpenHands Agent Canvas | Installed in Docker, bound to `127.0.0.1:3000`, connected to vLLM, and smoke-tested with file and shell tools in an isolated workspace. |
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

The vLLM command enables automatic tool choice with the `hermes` parser. These options are required for OpenHands tool calls. The current setup also uses `--enforce-eager`, disabling torch compilation and CUDA graph capture.

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

OpenHands Agent Canvas is installed from the pinned image `ghcr.io/openhands/agent-canvas@sha256:ad0829a7082a71ddfd2d16c1fae5a2172e4ca5a34eba7f03b69bd5b9b1bc54d7`. It is published only on `127.0.0.1:3000`. Its persistent settings and conversations are in `~/.local/share/openhands/state/`; the only mounted workspace is `~/.local/share/openhands/workspace/`, available inside the agent container as `/projects`. The Docker container is not privileged and has no Docker socket mount.

The container joins the `local-llm_default` Docker network, allowing it to reach vLLM at `http://vllm:8000/v1` while vLLM remains bound to host loopback. In OpenHands Advanced model settings, use model `openai/local-llm`, that base URL, and the placeholder API key `local-llm` (vLLM has no API-key authentication configured). Do not expose the unauthenticated vLLM service on a network interface.

The container runs as UID 10001. The state and workspace directories are owned by UID 10001 and shared with host group 1000 so the host user can inspect generated files. Files created by the agent may be mode 600; use `docker exec -u 0 openhands-canvas chmod 640 /projects/<file>` when host read access to an individual result is needed.

The installation was tested with the `local-llm` profile: OpenHands created `/projects/smoke-test.txt`, ran `pwd && cat /projects/smoke-test.txt`, and reported exit status 0. The host independently verified the file contents. Anonymous usage telemetry is disabled. For each real task, mount only the intended workspace, state its outcome and validation, inspect the resulting diff, and run the project's checks before accepting changes. Configure Qwen's chat template and non-thinking/tool-use settings, and retain at least the current 32k context window.

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

The tested OpenHands installation is suitable for initial local trials. Later role-specific harnesses can be evaluated when the specification and MCP model roles are ready to be staffed.

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
