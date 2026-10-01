# Commissioning work on the Spark

Roles are in [amms009.md](amms009.md). Area branches and worktrees are in [ampd004.md](ampd004.md).

## Default

A development task is done by a local agent on this DGX Spark, in the worktree and on the branch for that area. One area is in play in a worktree. The agent is told the role, the outcome, and the files or formal target it may change.

## Access to LLMs on the Spark

The Spark's services listen on loopback, so access them from another machine through an SSH tunnel. OpenHands Agent Canvas listens on port `3000`; the vLLM OpenAI-compatible API listens on port `8000`. The two ports serve different clients.

From the client machine, forward both ports in one SSH session:

```sh
ssh -N -L 3000:127.0.0.1:3000 -L 8000:127.0.0.1:8000 <user>@spark-95fb
```

Keep the SSH session open while using either service. Replace `<user>` with the Spark login; use the hostname or SSH alias configured for the Spark if `spark-95fb` does not resolve.

### OpenHands

Open `http://127.0.0.1:3000` in a browser on the client machine. OpenHands is already configured to use the vLLM service on the Spark's Docker network, so it does not need to connect through the client's port `8000` tunnel.

### Copilot Chat

VS Code Chat can use the Spark model as a custom endpoint. In VS Code, run **Chat: Manage Language Models**, choose **Add Models**, then **Custom Endpoint**. Select **Chat Completions** and configure the endpoint as `http://127.0.0.1:8000/v1/chat/completions`. When prompted for an API key, use `local-llm`; vLLM does not enforce API-key authentication, but the setup expects a value. Set the model ID to `local-llm` and enable tool calling to use the model in agent mode. Then select the added model in Chat's model picker.

This configures the chat and agent experience, not Copilot inline code completions. Copilot Business or Enterprise administrators may need to enable BYOK for the organization.

### Copilot CLI

Copilot CLI can use the same vLLM endpoint as a custom OpenAI-compatible provider. Keep the SSH tunnel to port `8000` open, then in another terminal on the client machine set:

```sh
export COPILOT_PROVIDER_BASE_URL=http://127.0.0.1:8000/v1
export COPILOT_PROVIDER_TYPE=openai
export COPILOT_MODEL=local-llm
copilot
```

vLLM does not require an API key, so `COPILOT_PROVIDER_API_KEY` can be left unset. Copilot CLI requires the selected model to support streaming and tool calling. Run `copilot help providers` for provider configuration details.


## Cloud models

Grok and Copilot in the cloud are used when a frontier model is likely to do the task better than the local models then available. The project manager applies that test to the task.

Cases that meet it at the start of this arrangement:

- Exploratory philosophy and architecture, and top-level strategy, while local models are not yet carrying those roles.
- Independent review of a pull request into `main` (Copilot code review).
- A bounded coding subcontract that the local models cannot yet finish (Copilot coding agent).

The test is reapplied as local models, including models fine-tuned for [SPaDE](../tlad001.md#spade), become able to hold the role. Admin documents are written by the project manager. That role may be filled in a Grok session while the work is still the liaison itself, and delegated to a local agent when the task is bounded.

## Review into `main`

Work that is to land on `main` is progressed on the area branch in its worktree and submitted as a pull request. Copilot code review is included on that pull request. The principal accepts the merge.

Detail of the review step is in [ampd005.md](ampd005.md). A pull request authored by the Copilot coding agent is reviewed by the principal. Copilot does not independently review a change it authored.

## Specialist subcontracts are GitHub Issues

A bounded specialist task is commissioned as a GitHub Issue. The issue names the role, the outcome, the files or formal target, and the acceptance check. The worker is a local agent, or the Copilot coding agent when the frontier-model test above says so. Copilot delegation, when chosen, follows [ampd001.md](ampd001.md) and [ampd008.md](ampd008.md).

The issue is the record of the subcontract. The worktree is the workplace. The pull request is the review. The issue links the branch.

Exploratory philosophy, architecture, and strategy are developed in conversation and recorded as `tlph`, `tlad`, and `ampl` documents, following [ampd003.md](ampd003.md). They are not opened as Issues in order to be discovered.

GitHub Projects, as in [ampl003.md](ampl003.md), may still group issues. The issue is the unit that is handed to a specialist.

---

Document ID: ampd009
Author: Grok Build (Grok 4.7)
Status: In progress
Chat log: [amcl003.md](amcl003.md)
