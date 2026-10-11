# Local agent task execution

## Purpose

This procedure governs bounded autonomous work by a local LLM on the DGX Spark. Interactive discussion, exploratory philosophy and architecture, difficult specification work, and escalation remain cloud-frontier work until local evaluation shows that a local role can discharge them reliably.

It complements [ampd009.md](ampd009.md): the Issue is the subcontract, the area worktree is the workplace, and the pull request is the review.

## Task description

Every task description for a local worker states:

1. The role, outcome, and files or formal target.
2. The area branch and its worktree.
3. The documents and sources the worker may read.
4. The files it may change.
5. The exact validation commands and the required result.

The worker does not infer a target, a branch, or an acceptance check that the task does not state.

## Worktree access

The worker receives one named area worktree, mounted in its agent workspace for that task. It receives no other project worktree, home directory, Docker socket, GitHub credential, or production SPaDE repository. The worker does not change branches in that worktree.

The mount is established and checked by the host-side task runner before the worker starts. The runner makes the worktree path and permitted validation commands explicit in the task prompt. One worker has write access to a worktree at a time.

## Validation and review

The worker runs the task's validation commands before proposing completion. For a HOL specification, this includes generating the SML from its markdown `hol` fences and checking it with ProofPower. For code derived from a specification, it includes the stated syntax, type, and alpha tests.

A worker that cannot obtain the required passing result stops, records the command output and changed files, and does not propose a pull request. Passing validation is necessary but not sufficient: the resulting area-branch change is reviewed by the principal and through the normal pull-request process before integration into `main`. A worker never merges into `main`.

## Adoption

This is a provisional procedure. The first task is run interactively enough to verify its mount, prompt, validation, and recording before unattended scheduling is enabled. The evaluation tasks in [ampl006.md](ampl006.md) determine which roles local models may subsequently hold.

---

Document ID: ampd010
Author: GitHub Copilot CLI (GPT-5.6 Terra)
Status: In progress
Chat log: [amcl003.md](amcl003.md)
