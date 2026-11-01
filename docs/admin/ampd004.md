# Task branches, worktrees, and sessions

## Introduction

SPaDE development is oriented towards agentic work and is managed through a heirarchic task structure executred in a combination of git branches, worktrees, and sessions, which together facilitate structured and coordinated agentic work.
There are a variety of different kinds of agents which can be applied to tasks, including human agents, cloud hosted frontier LLMs in suitable frameworks such as grok, and github copilot agents, open weight LLMs, some specially tuned on local servers, and the alpha-zero style reinforcement learning agents trained locally by specialised local LLMs.
Ultimately SPaDE development will substantially or wholly transfer into SPaDE repositories and revised procedures will be required, but now and throughout any transitional period the procedures defined here will apply to any work which involves changes to the SPaDE github repository.


This document describes the mechanics of setting up, managing, and concluding tasks within the SPaDE development framework, including the use of git branches, worktrees, and sessions to coordinate agentic work effectively.

- [Meta-Task-Descriptions](#meta-task-descriptions)
- [Task Descriptions](#task-descriptions)
- [Task Setup](#task-setup)
- [Task Completion](#the-main-checkout)

## Meta Task-Descriptions

Meta-task descriptions have been introduced to facilitate the application of agentic AI to commissioning work in an area of SPaDE development. There is one meta-task-description for each subsystem, which is held in the subsystem directory of the repository in a "td" document series as number zero.
Its purpose is to identify the tasks which need to be undertaken, sometimes in advance of availability of a full task description.
This permits the writing of task descriptions by agents.

Meta task-descriptions are not subject to the same degree of formality as individual task descriptions.

## Task Descriptions

We are experimenting with a formal structure for task descriptions in which yml is used to present the cannonical kinds of information needed to accomplish a task.
A sample is shown in [Proposal: Structured Project Data for SPaDE Repositories](amms013.md).
This formal structure should be presented at the head of the task description with further less formal explanations and context provided below it, however at this stage the exact format and required fields are still under experimentation, so the adoption is not expected to be uniform across all tasks.

Tasks will usually be documented and executed in stages, with the same task description covering all the stages.

## Task Setup

The setup for undertaking a task varies according to what kind of agent is performing the task.
Autonomous copilot agents are likely to undertake the task in a spade container on github servers.
Human agents may also prefer to work in the spade container.
In both cases, the container environment comes up ready to go (for development or build).

If tasks are undertaken by grok build or grok bot, or are initiated from agentic copilot chat or copilot CLI, then there is some uncertainty about how the agent will be working.
If the agent in those cases is operating in the same environment as the interactive session, then special steps, such as creating a task dedicated worktree, are necessary.
If a separate server or a separate login shell is used without using the SPaDE container, then the setup is more elaborate, since ProofPower will need to be installed and built first, and the spade database will need to be set up after building rbjhol.polydb in the retro directory.

Alongside the uncertainty about how the various agents are hosted, we expect continuous development of both grok and github products which may necessitate continuous adjustments to the workflow, and we will be seeking to run LLMs or focal AI on the DGX spark.

A task that will change the repository has one branch, one worktree, and the sessions that use that worktree. The branch is cut from `main`. The worktree is removed, and the branch is deleted, when the task's pull request is finished. Copilot's coding agent has the same branch lifetime and has no worktree on this machine ([ampd001.md](ampd001.md)).

## The main checkout

`~/git/SPaDE` stays on `main`.
Only in exceptional circumstances should changes be made directly in the main checkout. All task-specific work should be conducted in dedicated worktrees.

## Opening a task

The branch and the worktree share one name. When the task has a document, the name is that document's id (`tltd001`). Otherwise the task states a short hyphenated name.

From the main checkout:

```sh
git worktree add -b tltd001 ~/git/SPaDE-tltd001 main
```

Open the session with its working directory set to `~/git/SPaDE-tltd001`. `git worktree add -b` names the branch and places the worktree beside the main checkout.

The task states the files that may be changed. Where a kind of document belongs is in [amms001.md](amms001.md) and [amms009.md](amms009.md). `AGENTS.md` is the same text on every branch.

The worktree lasts for the whole task, including review. This will normally involve multiple stages, which are set out in the main task document. Several sessions may use it. The branch of a worktree stays as it is while a session has that directory as its working directory.

ProofPower work for the task uses a version of `spade.polydb`, in the worktree root. It is a child of `rbjhol.polydb` in $PPDIR/bld/db. `spade.polydb` remains the database for interactive development and for the build. `*.polydb` is gitignored. Removing the worktree removes the task database.

If `main` moves during the task, merge `main` into the task branch before the pull request is finished.

Outcomes that belong in the document hierarchy go into the hierarchy, not into `~/.grok/memory`.

Grok retained memory is in `~/.grok/memory/` (keyed on `origin`). Worktrees of this repo share that store. Grok sessions are under `~/.grok/sessions/`, keyed on the working directory, so each worktree has its own resume list. An empty `.grok/memory` under a checkout is not the store and is not in git.

## Closing a task

A task is closed when a pull request into its parent branch has been merged.
If the parent has moved during the task, merge the latest changes from the parent into the task branch before completing the pull request.
The pull request into `main` is the review ([ampd005.md](ampd005.md)). After it is merged, and after every session in the task directory has ended, run the following in `~/git/SPaDE`. The task directory is clean before it is removed.

```sh
git pull
git worktree remove ~/git/SPaDE-tltd001
git branch -d tltd001
git push origin --delete tltd001
```

Run the last command when the remote branch is still present.

A task closed without merging is removed in the same way. Delete its local branch with `git branch -D` when the branch has not been merged.

A worker does not merge, and does not remove the worktree or the branch. The host does that from the main checkout ([ampd010.md](ampd010.md)).

## Copilot

Copilot's coding agent creates its own branch and opens the pull request against `main`. It has no worktree on this machine. That branch is deleted when the pull request is merged.

Delegation workflow and templates: [ampd008.md](ampd008.md).

---

Document ID: ampd004
Author: Grok Build (Grok 4.7)
Status: In progress
Chat log: [amcl003.md](amcl003.md)
