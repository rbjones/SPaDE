# Task Description — pp-step, an interactive ProofPower session

## Purpose

The purpose of pp-step is to enable agents to undertake interactive sessions with ProofPower while developing proofs, primarily for use in the formal specification and metatheory of SPaDE.

Ultimately the formal metatheory will be conducted in SPaDE itself using the MCP interface supported by the SPaDE MCP server.
But in advance of that capability, agents need a way to interact with ProofPower directly to develop and check proofs.
This is to be done by providing a resident ProofPower session and a shell command, `pp-step`, that submits one Standard ML phrase and returns the text printed up to the next prompt.

Specification scripts can be written and checked by loading a file, as [tlci001.mkf](../tlci001.mkf) does. Proofs of the obligations in [amms012.md](amms012.md#consistency-proofs) need the goal stack between steps: a consistency proof before a constant is introduced, and the non-emptiness proof before a new type constructor. `pp-step` is how an agent conducts those proofs.

The facility is used across the system, so it lives under `docs/admin/`, with the `am` document codes in [amms001.md](amms001.md). It is not part of the knowledge repository.

## Not in this task

A separate task will investigate an MCP server that presents the same interface as a SPaDE native repository, with a ProofPower repository behind it. This task does not add that server, and it does not add tools to [mcpcd001.py](../../mcp/mcpcd001.py).

[krcd012.py](../../kr/krcd012.py) keeps a `pp` process for `NativeRepoService.repl` after loading `krcd011.sml`. That protocol stays as it is. `pp-step` does not enter it, and this task does not change `krcd012.py`.

## Workplaces

The editable files are the same for both runners. Checkout root means the directory `--root` selects: the root of the checkout the command is run in.

**Grok, on the host.** The branch and the worktree are `amtd006`, cut from `main` as in [ampd004.md](ampd004.md). The worktree is `~/git/SPaDE-amtd006`. Do the work there. The main checkout is not the workplace.

**Copilot, in the SPaDE container.** The container checkout is the workplace. Copilot creates the working branch and opens the pull request against `main`, as in [ampd008.md](ampd008.md). It does not create `~/git/SPaDE-amtd006`. The issue sets `base_ref: main` and links the copy of this document that is on `main`.

## Branch and files

Files that may be changed:

- `docs/admin/amcd005.py` — the session and the `pp-step` command
- `docs/admin/amte001.py` — the test
- `docs/admin/README.md` — index `amcd005.py` and `amte001.py`, and drop `amcd004.py` when that file is removed
- `docs/admin/amcd004.py` — remove this sketch once `amcd005.py` is the indexed implementation
- `kr/README.md` — mark `krcd013.py` obsolete, as below
- `Makefile` — only if the `spade.ldd` recipe writes a database under `$PPDIR` or uses a stem other than `spade`

No other files. Do not add `kr/krcd014.py`, `kr/krte007.py`, or a copy of the command under `common/`. Do not delete `kr/krcd013.py`. Do not run `make rbjhol.ldd`.

`kr/krcd013.py` is the same sketch as `amcd004.py` and is not the interface. It is absent from [kr/README.md](../../kr/README.md). Add it to the code list, in numerical order after `krcd012.py`, with the link struck through, as [amms001.md](amms001.md) specifies for a file that is kept but retired:

```markdown
- ~~[krcd013.py](krcd013.py)~~ - Python interface to an interactive theorem prover (obsolete; the session is `docs/admin/amcd005.py`)
```

## Environment

`PPDIR` is already set. On this host it is `/home/rbj/git/pp`. In the SPaDE container it is `/proofpower-source`. Those are examples. No check compares `PPDIR` with either string.

The frozen parent is `$PPDIR/bld/db/rbjhol.polydb`. It already exists. This task does not build it.

`pp` and `pp_make_database` are on `PATH`. If `pp` is not on `PATH` and `$PPDIR/dev_env` exists, source that script before the acceptance command, as [SPaDE_Test_arm.yml](../../.github/workflows/SPaDE_Test_arm.yml) does. The test does not search a hardcoded directory for the binaries.

## Command

`pp-step` is `python3 docs/admin/amcd005.py`, run from the repository root. The first invocation starts the session. Each later invocation uses that same process.

```sh
python3 docs/admin/amcd005.py '1 + 1;'
python3 docs/admin/amcd005.py stop
```

A phrase may be given on standard input instead of as an argument, so that a phrase of more than one line is one submission. One invocation submits one phrase. The command does not split the text on semicolons.

`pp` is started on the checkout's own `spade.polydb`, as specified below, with no `-f`, so it reads the interactive stream. `PPDIR` and `PATH` are those from the environment section. If `PPCHARSET` is unset, the command sets it to `utf8`. `--root DIR` selects the checkout root. The default is the root of the checkout that contains the current directory.

The session process puts that root first on `PPDATABASEPATH`, as [spade_env.sh](../../spade_env.sh) does, and starts `pp -d spade`. The caller does not have to source `spade_env.sh` before `pp-step`.

The process is attached to a pseudo-terminal. A pipe is not sufficient: Poly/ML block-buffers a non-terminal, and a prompt need not end with a newline. Output written by ProofPower on either standard stream is part of the returned text.

The ready prompt and the continuation prompt are whatever this `pp` prints. The marker suggested in `krcd013.py` is not a requirement. If the process is sitting at a continuation prompt, return the text so far and exit within 10 seconds; do not wait for a ready prompt that will not come until the caller sends the rest of the phrase. The session stays up. The next invocation submits the rest of the phrase.

`stop` ends the process. It does not send `save`, `save_and_quit`, or `save_and_exit`. The database is left as it was when the process started, unless a phrase the caller submitted saved it. `new_SPaDE_theory` in [tlcd002.md](../tlcd002.md) removes any theory hierarchy hanging from `SPaDEroot` before creating the theory again, and Poly/ML accepts a new definition of an SML function, so the session does not need a save protocol.

If `pp` or `pp_make_database` is not on `PATH`, the command exits with a non-zero status and names the missing program.

## One database name in every checkout

The database is always `spade.polydb`. The same name is used in every checkout. The makefile already passes that stem to `pp -d`. A task does not invent another stem, and `pp-step` has no `--database` option.

Each checkout has its own file, at the checkout root. It is a child of `rbjhol`. Creating it reads `rbjhol` and does not save `rbjhol`, and it does not write `$PPDIR/bld/db/spade.polydb`. `rbjhol` is the database at `$PPDIR/bld/db/rbjhol.polydb`.

The child is created from the checkout root with:

```sh
pp_make_database -p rbjhol spade
```

The `spade.ldd` recipe in the root [Makefile](../../Makefile) does this and does not copy the file under `$PPDIR`. Change that recipe only if it writes a database under `$PPDIR` or uses another stem. Do not run `make` or `make spade.ldd` to prove it: a checkout without a `rbjhol.ldd` stamp would rebuild `rbjhol`. To start again from `rbjhol`, recreate the child with `pp_make_database -f -p rbjhol spade` in that same root.

If `spade.polydb` is absent when `pp-step` is first invoked, `pp-step` creates it by that same command. It opens the checkout file, not `$PPDIR/bld/db/spade.polydb`. The session checks in the test use a temporary `--root`, so the runner's own `spade.polydb` is not the database under test.

The child contains the theories of `rbjhol`: the `maths_egs` material, the `spc` series, and the `np` material, including `rbjmisc`. A theory that has been saved only into some other `spade.polydb`, including `SPaDEroot`, is not in this child. The caller creates or opens the theories the task needs.

`*.polydb` is already listed in `.gitignore`. The child is not committed. Leave `.gitignore` unchanged unless that line is missing. Removing a host worktree removes its child, as in [ampd004.md](ampd004.md).

One agent uses a checkout's `spade.polydb` at a time. An exclusive advisory lock is held on `spade.pid` in that same directory for the whole session, taken before `pp` is started and released at `stop` or if the session process dies. `.gitignore` already ignores `*.pid`. A second `pp-step` for the same `--root` exits with a non-zero status, reports that the database is in use, and does not start `pp`. Another checkout has its own `spade.polydb` and its own lock, and a session there is not refused.

Direct use of `pp -d spade`, outside `pp-step`, still depends on sourcing `spade_env.sh` so the checkout root is on `PPDATABASEPATH`.

## What the session keeps

Across calls, until `stop`:

- the open theory and the theory hierarchy in that process
- SML bindings, including a redefinition of a function
- the subgoal-package goal stack

The command does not itself open a theory or set a goal. The caller does.

## Test

Both runners use the same command, from the checkout root, with `PPDIR` set and `pp` on `PATH`:

```sh
python3 docs/admin/amte001.py
```

`docs/admin/amte001.py` uses a temporary directory as `--root`. The database under that root is `spade.polydb`. The parent is `$PPDIR/bld/db/rbjhol.polydb`, which is already frozen. A missing `PPDIR`, a missing parent file, or a missing `pp` or `pp_make_database` is a failure, and the message names the missing item. The test does not skip. It is not added to `PYTEST` in `kr/krci001.mkf`, so a normal `make` on a machine without ProofPower does not run it.

The test does all of the following in one session, then stops the session:

- Submit `val n = 1;` and then `n + 1;`. The second result depends on `n`.
- Submit `val k =`. The command returns within 10 seconds while `pp` is still running at a continuation prompt. Then submit `1;` and then `k;`. The value of `k` is 1.
- Submit a `set_goal` and then one tactic. The tactic's transcript is the goal state after that tactic, and it contains no second startup banner.
- Submit a phrase that contains `│`. The session accepts it under `PPCHARSET=utf8`.
- While that session is alive, a second `pp-step` on the same `--root` exits with a non-zero status and does not start a second `pp`.
- While that session is alive, a `pp-step` on a different `--root` is not refused and starts its own session. Stop that second session before continuing.
- `stop`, and assert that the `pp` process has exited and the lock is released.
- After `stop`, a new session on the same `spade.polydb` starts.
- Assert that the test did not send `save`, `save_and_quit`, or `save_and_exit`.
- Assert that the database file is `<root>/spade.polydb`.
- Assert that `$PPDIR/bld/db/rbjhol.polydb` is byte-for-byte unchanged.
- Assert that `$PPDIR/bld/db/spade.polydb` is unchanged if it was present, and still absent if it was absent.

If a pseudo-terminal cannot be opened, the test fails at that point and names the failure. It does not hang and it does not skip.

## Acceptance

- `python3 docs/admin/amte001.py` passes with `PPDIR` set and `pp` on `PATH`.
- A second session on the same checkout's `spade.polydb` is refused while the first holds the lock, and a session in another checkout is not refused.
- `docs/admin/README.md` lists `amcd005.py` and `amte001.py`, and no longer lists `amcd004.py`.
- `kr/README.md` lists `krcd013.py` with the link struck through, and `kr/krcd013.py` is still present.

---

Document ID: amtd006
Author: Grok Build (Grok 4.7)
Status: Ready
