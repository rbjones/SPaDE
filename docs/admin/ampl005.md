# Immediate plan: Grok Build/ Copilot app evaluation

This is the short plan for the period in which SPaDE is evaluating ways of working which facilitate fuller involvement of AI in the development.

The working split is in [README.md](README.md): Grok Build for interactive and high-level work (memory in `~/.grok`); Copilot for GitHub-scheduled agentics, tested in the SPaDE container; Copilot code review of Grok-authored PRs as a third use. Area worktrees remain ([ampd004.md](ampd004.md)). Longer strategy remains in [ampl001.md](ampl001.md), [ampl002.md](ampl002.md), and [ampl004.md](ampl004.md).

## Now (`am`)

1. Document methods: worktrees, branch ownership, what Grok may edit, memory vs `docs/`.
2. Align `AGENTS.md` with those methods (conservative on `main`; relaxed per area branch).
3. `drafts/` removed. Living documents it listed are in `docs/`. Grok web share URLs are in [amcl002.md](amcl002.md).
4. Keep the `ampl*` plans in `docs/admin/` consistent with top-level strategy; do not edit `docs/tlpl001.md` from `am`.
5. Land coherent `am` units on `main` by pull request, with Copilot as independent reviewer ([ampd005.md](ampd005.md)). Do not treat Copilot Chat as a substitute for that PR review.

## Next (`kr`)

KR-specific architecture, design, and prototype work lives in `kr/` and is **not blocked** on completing system-wide `docs/` architecture ([amms001.md](amms001.md)).

1. Proceed from existing `kr/` material (`krad*`, `krhd*`, prototype notes).
2. Keep `docs/tlad012.md` as the **cross-subsystem** catalogue of KR structures and interfaces (because other subsystems must see them), reconciled with `kr/krad001.md` — not as a substitute for KR-local design.
3. KR-local philosophy (`krph*`) stays with `kr`, not with synthetic-philosophy.

## Then (`mcp`)

1. v0 is a read-only projection of KR operations, specified before further coding.
2. Review `mcp-gpt-5.1-Codex-Max` (CLI/env/tests) in the MCP worktree; merge, cherry-pick, or drop.

## Parallel, not blocking

- Synthetic philosophy (`docs/tlph*`) as a standing area when wanted.
- Glossary as a method, or a short pass, not a fifth long-lived parallel branch.
- Revisions to glossary maintenance procedures are deferred unless urgent, and should be resumed after KR progress restarts.
- `dk` and `di` later, as in the existing onion (`ampl001`).

## Done enough to leave `am` as the bottleneck

A new Grok session, started in a worktree, can read [README.md](README.md) (working practice), [ampd004.md](ampd004.md) and `AGENTS.md` and know which files it may change, and this file for what to do next.
