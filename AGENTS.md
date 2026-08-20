# Agents Documentation

The SPaDE project is a philosophically grounded development of a widely distributed repository of declarative knowledge, together with (initially) Alpha-zero like intelligence supporting deductive reasoning and problem solving in the perfect information spaces determined by each context in the repository.

To understand the nature of the project it is necessary to start with the top-level README.md, and recursively chase through all the local links to .md files.
Alternative read all the .md files in the SPaDE repository!
Bearing in mind that this material is as yet far from complete.

Extensive further discussion is necessary to complete the philosophical background, architectural rationale and detailed design of the SPaDE project, and to provide a basis for the implementation of the SPaDE MCP server and the various other subsystems of SPaDE to which it provides access.

The upshot of such discussions should always be fitted appropriately into this document hierarchy, and the ~/.grok/memory directory should only be used for things which do not belong there, such as tracking work in progress, and achieving continuity between chat sessions.

As working practices evolve this document should be augmented or amended appropriately.

At this stage in the project, priority attaches exclusively to making the philosophical and architectural documentation in the docs directory adequate for the resumption of work on the design and implementation of the SPaDE knowledge respository and delivery of its capabilities through the SPaDE MCP server.

On the `am` branch (this worktree), Grok may amend `docs/admin/`, `AGENTS.md`, `reviews/`, and `.grok/`. Do not amend other trees unless explicitly asked.

Session layout, branch ownership, and merge practice: [docs/admin/ampd004.md](docs/admin/ampd004.md). Immediate plan: [docs/admin/ampl005.md](docs/admin/ampl005.md).

On `main`, Grok remains conservative: discuss and assess; write reviews and `.grok/` only, unless the user overrides.
