# Grok Build: branches, worktrees, and sessions

This is a first account of how SPaDE is to be developed with Grok Build, while methods are still being revised. It supersedes, for Grok, the Copilot-agent task assignment notes in [ampd001.md](ampd001.md) and [ampd002.md](ampd002.md) insofar as those assume a single checkout and GitHub Copilot.

## One focus per branch and worktree

Work is split into a small number of standing areas. Each area has:

- a **git branch** named for the area (no slash in the name if that would block a later `docs` branch);
- a **sibling git worktree**, not a second clone, e.g. `/Users/rbj/git/SPaDE-am` beside `/Users/rbj/git/SPaDE`;
- **Grok sessions whose cwd is that worktree**.

`main` is the integration branch. Do not check out another branch in a worktree that already has a live Grok session. Create or switch worktrees instead (`git worktree add`).

Clones and worktrees of this repo share one Grok memory directory (keyed on `origin`). Memory is for WIP and session continuity. Outcomes that belong in the document hierarchy go into the hierarchy, not into `~/.grok/memory`.

## Standing areas (provisional)

Open only what is needed. Do not create every worktree at once.

| Area | Branch | Worktree (proposed) | Owns |
|---|---|---|---|
| Administration | `am` | `…/SPaDE-am` | `docs/admin/`, `AGENTS.md`, plans, methods, Grok/session rules; `drafts/` phase-out |
| Knowledge repository | `kr` | `…/SPaDE-kr` | `kr/` plus KR-facing system docs, especially `docs/tlad012.md` |
| Synthetic philosophy | `synthetic-philosophy` | `…/SPaDE-sp` | system-wide `docs/tlph*` (not `kr/krph*` unless agreed) |
| MCP | `mcp` | `…/SPaDE-mcp` | `mcp/`; inspect `mcp-gpt-5.1-Codex-Max` before new coding |
| Glossary | (time-boxed, not standing) | — | term/anchor work rides on the branch that needs it; methods stay in [amms006](amms006.md) / [amms007](amms007.md) |
| Deductive kernel / intelligence | `dk`, `di` | later | after KR/MCP have a usable core |

Top-level documentation strategy (`docs/tlpl001.md`) and prototyping plans (`ampl001` and successors) are owned on `am`.

## What a session may edit

`AGENTS.md` on `main` remains conservative (discussion, assessment, reviews, `.grok/`). On an area branch, that file is relaxed **for that area** so the work can actually be written. Do not use an `am` session to rewrite `kr/` or `mcp/` except by explicit request.

On this `am` branch, Grok may edit `docs/admin/`, `AGENTS.md`, `reviews/`, and `.grok/`. Other trees only if asked.

## Starting and ending sessions

1. Open Grok with cwd set to the worktree (not to `main` unless integrating).
2. If memory is enabled, `/flush` before leaving a session that decided anything that is not yet in the docs.
3. Merge to `main` when a coherent unit is ready; do not accumulate unrelated work on `am`.

## Auth and spend

Grok Build may authenticate with OAuth (X Premium) or an API key. A stored OAuth session in `~/.grok/auth.json` wins over `XAI_API_KEY` until `grok logout`. Check `/session-info` (`Auth method`) if spend is in doubt.
