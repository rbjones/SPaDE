# Task branches, worktrees, and sessions

How Grok and Copilot are used is in the working-practice section of [README.md](README.md). This document is branches, worktrees, and sessions.

A task that will change the repository has one branch, one worktree, and the sessions that use that worktree. The branch is cut from `main`. The worktree is removed, and the branch is deleted, when the task's pull request is finished. Copilot's coding agent has the same branch lifetime and has no worktree on this machine ([ampd001.md](ampd001.md)).

## The main checkout

`~/git/SPaDE` stays on `main`. `main` is pulled there. Task worktrees are added and removed from there. Commits for a task are made in the task worktree.

## Opening a task

The branch and the worktree share one name. When the task has a document, the name is that document's id (`tltd001`). Otherwise the task states a short hyphenated name.

From the main checkout:

```sh
git worktree add -b tltd001 ~/git/SPaDE-tltd001 main
```

Open the session with its working directory set to `~/git/SPaDE-tltd001`. `git worktree add -b` names the branch and places the worktree beside the main checkout.

The task states the files that may be changed. Where a kind of document belongs is in [amms001.md](amms001.md) and [amms009.md](amms009.md). `AGENTS.md` is the same text on every branch.

The worktree lasts for the whole task, including review. Several sessions may use it. The branch of a worktree stays as it is while a session has that directory as its working directory.

If `main` moves during the task, merge `main` into the task branch before the pull request is finished.

Outcomes that belong in the document hierarchy go into the hierarchy, not into `~/.grok/memory`.

Grok retained memory is in `~/.grok/memory/` (keyed on `origin`). Worktrees of this repo share that store. Grok sessions are under `~/.grok/sessions/`, keyed on the working directory, so each worktree has its own resume list. An empty `.grok/memory` under a checkout is not the store and is not in git.

## Closing a task

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
