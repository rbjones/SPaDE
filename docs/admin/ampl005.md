# Immediate plan: Grok Build transition

This is the short plan for the period in which SPaDE is moving from Copilot-centred practice to Grok Build, with one focus per branch and worktree. Longer strategy remains in [ampl001.md](ampl001.md), [ampl002.md](ampl002.md), and [ampl004.md](ampl004.md). Session mechanics are in [ampd004.md](ampd004.md).

## Now (`am`)

1. Document methods: worktrees, branch ownership, what Grok may edit, memory vs `docs/`.
2. Align `AGENTS.md` with those methods (conservative on `main`; relaxed per area branch).
3. Decide the fate of `drafts/` (phase out: remaining links into `docs/` / chat logs, then remove).
4. Keep `docs/tlpl001.md` and the `ampl*` plans pointing at each other so documentation strategy and prototyping strategy do not drift.

## Next (`kr`)

1. Treat `docs/tlad012.md` as the system-wide KR abstract model, reconciled with `kr/krad001.md`.
2. KR-local philosophy (`krph*`) stays with `kr`, not with synthetic-philosophy.

## Then (`mcp`)

1. v0 is a read-only projection of KR operations, specified before further coding.
2. Review `mcp-gpt-5.1-Codex-Max` (CLI/env/tests) in the MCP worktree; merge, cherry-pick, or drop.

## Parallel, not blocking

- Synthetic philosophy (`docs/tlph*`) as a standing area when wanted.
- Glossary as a method, or a short pass, not a fifth long-lived parallel branch.
- `dk` and `di` later, as in the existing onion (`ampl001`).

## Done enough to leave `am` as the bottleneck

A new Grok session, started in a worktree, can read `ampd004.md` and `AGENTS.md` and know which files it may change, and `ampl005.md` for what to do next.
