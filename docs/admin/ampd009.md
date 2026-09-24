# Commissioning work on the Spark

Roles are in [amms009.md](amms009.md). Area branches and worktrees are in [ampd004.md](ampd004.md).

## Default

A development task is done by a local agent on this DGX Spark, in the worktree and on the branch for that area. One area is in play in a worktree. The agent is told the role, the outcome, and the files or formal target it may change.

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
