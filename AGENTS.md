# Agents Documentation

The SPaDE project is a philosophically grounded development of a widely distributed repository of declarative knowledge, together with (initially) Alpha-zero like intelligence supporting deductive reasoning and problem solving in the perfect information spaces determined by each context in the repository.

To understand the project, start with the top-level README.md and follow its links. The administrative documents are indexed in [docs/admin/README.md](docs/admin/README.md). This file is only for instructions specific to Grok Build (and similar agents). Do not put project-wide procedures here.

The upshot of discussions belongs in the document hierarchy. Grok memory is `~/.grok/memory` (not a `.grok/` directory in the worktree). It is only for work in progress and continuity between chat sessions.

Grok Build may authenticate with OAuth (X Premium) or an API key. A stored OAuth session in `~/.grok/auth.json` wins over `XAI_API_KEY` until `grok logout`. Check `/session-info` (`Auth method`) if spend is in doubt.

Be concise. Record the **endpoint** of a discussion (the decision, placement, or procedure as it now stands), not the path that led there. Do not expand admin or other docs with blow-by-blow of how a wording was reached.

Amend this file only when the advice is particular to Grok (or a similar agent). Everything else goes under `docs/admin/`.
