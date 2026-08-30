# Branches, worktrees, and sessions

## Introduction

Substantial areas of work should be conducted on a new branch with a corresponding worktree and session, so that work in progress in one area does not interfere with work in another area.
Work will in one area will not affect work in another area until it has been merged into main (usually via a pull request), and then back into the other areas worktree.

Each area has:

- a **git branch** named for the area;
- a **sibling git worktree**, not a second clone, e.g. `/Users/rbj/git/SPaDE-am` beside `/Users/rbj/git/SPaDE`;
- **Chat sessions (grok build or copilot) whose cwd is that worktree**.

`main` is the integration branch. Do not check out another branch in a worktree that already has a live Chat session. Create or switch worktrees instead (`git worktree add`).

Clones and worktrees of this repo share one Grok memory directory (keyed on `origin`).
Memory in copilot will span all work under github rbjones.
is for WIP and session continuity. Outcomes that belong in the document hierarchy go into the hierarchy, not into `~/.grok/memory`.

## Standing areas (provisional)

Open only what is needed.
Do not create every worktree at once.

| Area | Branch | Worktree (proposed) | Owns |
| --- | --- | --- | --- |
| Philosophy and Architecture | `pa` | `…/SPaDE-pa` | system-wide `docs/tlph*` |
| Administration | `am` | `…/SPaDE-am` | Administrative materials only: `docs/admin/`, `AGENTS.md`, `reviews/`, `.grok/`; `drafts/` phase-out. **Not** `docs/tlph*`, `docs/tlad*`, `docs/tlpl*`, or other system-wide philosophy/architecture. |
| Knowledge repository | `kr` | `…/SPaDE-kr` | `kr/` |
| MCP | `mcp` | `…/SPaDE-mcp` | `mcp/` |
| Deductive kernel | `dk` | .../SPaDE-dk | `dk/` |
| Deductive intelligence | `di` | `…/SPaDE-di` | `di/` |

Admin plans and methods (`ampl*` and the rest of `docs/admin/`) are owned on `am`. Top-level documentation strategy in `docs/tlpl001.md` is **not** an `am` file.

## What a session may edit

`AGENTS.md` on `main` remains conservative (discussion, assessment, reviews, `.grok/`). On an area branch, that file is relaxed **for that area** so the work can actually be written. Do not use an `am` session to rewrite `kr/` or `mcp/` except by explicit request.

On this `am` branch, Grok may edit `docs/admin/`, `AGENTS.md`, `reviews/`, and `.grok/`. Other trees only if asked.

## Starting and ending sessions

1. Open Grok with cwd set to the worktree (not to `main` unless integrating).
2. If memory is enabled, `/flush` before leaving a session that decided anything that is not yet in the docs.
3. Merge to `main` when a coherent unit is ready; do not accumulate unrelated work on `am`. Preferred path: a pull request into `main` with GitHub Copilot as an independent reviewer — [ampd005.md](ampd005.md).

For Copilot coding-agent delegation workflow and templates (task document, issue body, and delegation prompt), see [ampd008.md](ampd008.md).

## Auth and spend

Grok Build may authenticate with OAuth (X Premium) or an API key. A stored OAuth session in `~/.grok/auth.json` wins over `XAI_API_KEY` until `grok logout`. Check `/session-info` (`Auth method`) if spend is in doubt.
