# Immediate plan: Grok Build/ Copilot app evaluation

How the team now works on the DGX Spark is in [amms009.md](amms009.md), [ampl006.md](ampl006.md), and [ampd009.md](ampd009.md). The subsystem order below stands until the architect replaces it.

This is the short plan for the period in which SPaDE is evaluating ways of working which facilitate fuller involvement of AI in the development.

Each task has its own branch and worktree ([ampd004.md](ampd004.md)). Longer strategy remains in [ampl001.md](ampl001.md), [ampl002.md](ampl002.md), and [ampl004.md](ampl004.md).

## Administration

1. Methods for branches, worktrees, and sessions are in [ampd004.md](ampd004.md). The task states the files that may be changed. Memory stays in `~/.grok`; outcomes go in `docs/`.
2. `AGENTS.md` is the same text on every branch.
3. `drafts/` removed. Living documents it listed are in `docs/`. Grok web share URLs are in [amcl002.md](amcl002.md).
4. Keep the `ampl*` plans in `docs/admin/` consistent with top-level strategy. `docs/tlpl001.md` remains the top-level documentation strategy.
5. Land each task on `main` by pull request, with Copilot as independent reviewer ([ampd005.md](ampd005.md)). Do not treat Copilot Chat as a substitute for that PR review.

## Next (knowledge repository)

KR-specific architecture, design, and prototype work lives in `kr/` and is **not blocked** on completing system-wide `docs/` architecture ([amms001.md](amms001.md)).

1. Proceed from existing `kr/` material (`krad*`, `krhd*`, prototype notes).
2. Keep `docs/tlad012.md` as the **cross-subsystem** catalogue of KR structures and interfaces (because other subsystems must see them), reconciled with `kr/krad001.md` — not as a substitute for KR-local design.
3. KR-local philosophy (`krph*`) stays with `kr`, not with synthetic-philosophy.

## Then (MCP)

1. v0 is a read-only projection of KR operations, specified before further coding.
2. Review `mcp-gpt-5.1-Codex-Max` (CLI/env/tests) on a task branch; merge, cherry-pick, or drop.

## Parallel, not blocking

- Synthetic philosophy (`docs/tlph*`) when wanted, on a task branch of its own.
- Glossary as a method, or as a task whose branch is removed when its pull request is merged.
- Revisions to glossary maintenance procedures are deferred unless urgent, and should be resumed after KR progress restarts.
- `dk` and `di` later, as in the existing onion (`ampl001`).

## Done enough to leave administration as the bottleneck

A new Grok session, started in a task worktree, can read [README.md](README.md), [ampd004.md](ampd004.md), and `AGENTS.md`. The task states which files it may change. This file says what to do next.
