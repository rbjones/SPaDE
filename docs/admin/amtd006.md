# Task Description — pp-step, an interactive ProofPower session

## Purpose

The purpose of pp-step is to enable agents to undertake interactive sessions with ProofPower while developing proofs, primarily for use in the formal specification and metatheory of SPaDE.

Ultimately the formal metatheory will be conducted in SPaDE itself using the MCP interface supported by the SPaDE MCP server.
But in advance of that capability, agents need a way to interact with ProofPower directly to develop and check proofs.
This is to be done by providing a resident ProofPower session and a shell command, `pp-step`, that submits one Standard ML phrase and returns the text printed up to the next prompt.

Specification scripts can be written and checked by loading a file, as [tlci001.mkf](../tlci001.mkf) does. Proofs of the obligations in [amms012.md](amms012.md#consistency-proofs) need the goal stack between steps: a consistency proof before a constant is introduced, and the non-emptiness proof before a new type constructor. `pp-step` is how an agent conducts those proofs.

## Not in this task

A separate task will investigate an MCP server that presents the same interface as a SPaDE native repository, with a ProofPower repository behind it. This task does not add that server, and it does not add tools to [mcpcd001.py](../../mcp/mcpcd001.py).

## Branch and files

The branch and worktree are `amtd007`, cut from `main` as in [ampd004.md](ampd004.md).

Files that may be changed:

- `amcd005.py` — the session and the `pp-step` command
- `amte001.py` — the test
- `README.md` — index the new files
- `amcd004.py` — remove this sketch once `amcd005.py` is the indexed implementation

No other files.

## Command

`pp-step` is `python3 kr/krcd014.py`, run from the repository root with `PYTHONPATH` set so that `kr` imports. The first invocation starts the session. Each later invocation uses that same process.

```sh
python3 kr/krcd014.py '1 + 1;'
python3 kr/krcd014.py stop
```

A phrase may be given on standard input instead of as an argument, so that a phrase of more than one line is one submission. One invocation submits one phrase. The command does not split the text on semicolons.

`pp` is started on the worktree's own database, as specified below, with no `-f`, so it reads the interactive stream. `PPDIR` and `PATH` are those already used to load the docs theories. If `PPCHARSET` is unset, the command sets it to `utf8`. `--root DIR` selects the worktree root. The default is the root of the checkout that contains the current directory.

The process is attached to a pseudo-terminal. A pipe is not sufficient: Poly/ML block-buffers a non-terminal, and a prompt need not end with a newline. Output written by ProofPower on either standard stream is part of the returned text.

The ready prompt and the continuation prompt are whatever this `pp` prints. The marker suggested in `krcd013.py` is not a requirement. If the process is sitting at a continuation prompt, return the text so far and exit; do not wait for a ready prompt that will not come until the caller sends the rest of the phrase.

`stop` ends the process. It does not send `save`, `save_and_quit`, or `save_and_exit`. The child database is left as it was when the process started, unless a phrase the caller submitted saved it. `new_SPaDE_theory` in [tlcd002.md](../tlcd002.md) removes any theory hierarchy hanging from `SPaDEroot` before creating the theory again, and Poly/ML accepts a new definition of an SML function, so the session does not need a save protocol.

If `pp` or `pp_make_database` is not on `PATH`, the command exits with a non-zero status and names the missing program.

## One database per task

`spade.polydb` stays the database for interactive development and for the build. A `pp-step` session does not open it.

[retro/retro.mkf](../../retro/retro.mkf) makes `spade` with `pp_make_database -p rbjhol spade`. That first child freezes the theory hierarchy in `rbjhol`. `rbjhol` is not used again by the SPaDE build. Each task database is a further child of `rbjhol`, so creating one reads `rbjhol` and does not save it, and it does not freeze or write `spade.polydb`.

The database stem is the task id. [ampd004.md](ampd004.md) gives the branch and the worktree that id. The file is `<id>.polydb` in the worktree root, and `pp` is given that file as `-d`. `--database STEM` overrides the stem, which the test uses. When the file is absent, the first `pp-step` in that worktree creates it from the worktree root:

```sh
pp_make_database -p rbjhol tltd001
```

`rbjhol` is found through `PPDIR`, as the docs makefile finds it. To start the task again from `rbjhol`, recreate the child with `pp_make_database -f -p rbjhol <id>`.

The child contains the theories of `rbjhol`: the `maths_egs` material, the `spc` series, and the `np` material, including `rbjmisc`. A theory that has been saved only into `spade`, including `SPaDEroot`, is not in the child. The caller creates or opens the theories the task needs.

`*.polydb` is already listed in `.gitignore`. The child is not committed. Leave `.gitignore` unchanged unless that line is missing. Removing the worktree removes the child, as in [ampd004.md](ampd004.md).

One agent uses a task database at a time. An exclusive advisory lock is held on a sibling lock file for the whole session, taken before `pp` is started and released at `stop` or if the session process dies. The lock file name ends in `.pid`, which `.gitignore` already ignores. A second `pp-step` for the same database exits with a non-zero status, reports that the database is in use, and does not start `pp`. Another task has its own child of `rbjhol` and its own lock.

## What the session keeps

Across calls, until `stop`:

- the open theory and the theory hierarchy in that process
- SML bindings, including a redefinition of a function
- the subgoal-package goal stack

The command does not itself open a theory or set a goal. The caller does.

[krcd012.py](../../kr/krcd012.py) already keeps a `pp` process, for `NativeRepoService.repl` after loading `krcd011.sml`. That protocol stays as it is. `pp-step` does not enter it.

## Test

`kr/krte007.py` skips, as [krte005.py](../../kr/krte005.py) does, when `pp` or `pp_make_database` is not on `PATH`. It uses a temporary directory as `--root` and a stem passed with `--database`. The parent is the installed `rbjhol`, which is already frozen. Otherwise it does all of the following in one session, then stops the session:

- Submit `val n = 1;` and then `n + 1;`. The second result depends on `n`.
- Submit a `set_goal` and then one tactic. The tactic's transcript is the goal state after that tactic, and it contains no second startup banner.
- Submit a phrase that contains `│`. The session accepts it under `PPCHARSET=utf8`.
- While that session is alive, a second `pp-step` on the same `--root` exits with a non-zero status and does not start a second `pp`.
- `stop`, and assert that the `pp` process has exited and the lock is released.
- After `stop`, a new session on the same child starts.
- Assert that the test did not send `save`, `save_and_quit`, or `save_and_exit`.
- Assert that the child file is under the temporary directory and is named from the stem passed with `--database`.
- Assert that `$(PPDIR)/bld/db/rbjhol.polydb` and `$(PPDIR)/bld/db/spade.polydb` are unchanged.

The test is run directly. It is not added to `PYTEST` in `kr/krci001.mkf`.

## Acceptance

- The test passes with `PPDIR=/home/rbj/git/pp` and `pp` on `PATH`.
- A second session on the same task database is refused while the first holds the lock, and a session for another task is not refused.
- `kr/README.md` lists `krcd014.py` and `krte007.py`, and no longer presents `krcd013.py` as the interface.

---

Document ID: amtd007
Author: Grok Build (Grok 4.7)
Status: Ready
