# Review: Adequacy of `docs/` for Resuming KR and MCP Work

**Date**: 2026-08-20
**Time (UTC)**: 18:18
**Reviewer**: Grok 4.6 (Grok Build session in `/Users/rbj/git/SPaDE`)
**Scope**: Philosophical and architectural documentation in `docs/`, judged against the bar in `Agents.md` and `drafts/README.md`. Code in `kr/` and `mcp/` was used only as a check on whether the docs would let an AI resume that work without inventing policy.
**Constraint**: Assessment only. No edits were made under `docs/`.

## Verdict

The documentation is **not adequate** to resume detailed design and implementation of the knowledge repository, nor to specify how those capabilities should be delivered through the SPaDE MCP server.

Philosophy is closer than architecture. Architecture is closer to a table of contents than a design. Prototype code in `kr/` and `mcp/` is ahead of the top-level account that is supposed to govern it.

The bar, in the project's own words, is that AI should be able to progress detailed design and coding from the docs. That requires, at minimum:

1. A stable vocabulary of KR objects and operations.
2. A statement of what the MCP server exposes of those operations, and what it does not.
3. Enough kernel and trust policy that theorems, signatures, and contexts can be designed without inventing authority rules.
4. A readable path from purpose → architecture → those interfaces, without forcing the reader through every historical and evolutionary essay first.

Items 1–3 are not met. Item 4 is only partly met.

## What was inspected

- Top-level `README.md`, `docs/README.md`, `drafts/README.md`, `Agents.md`.
- Philosophy series `tlph001`–`tlph025` (line counts and the longer pieces in full or in substantial part).
- Architecture series `tlad001`–`tlad014`, especially `tlad003`, `tlad005`, `tlad011`–`tlad014`.
- Formal spec stub `tlcd001.md`, plan `tlpl001.md`, admin plan `docs/admin/ampl001.md`.
- `kr/README.md`, `kr/krad001.md` (opening), `mcp/README.md`.
- Working-tree state on 2026-08-20: uncommitted philosophy edits (notably `tlph021.md`), new `tlph023`–`tlph025`, `drafts/README.md` updates.

This is not a link audit and not a code review.

## Strengths

- The **purpose** is stated plainly (`tlph012`, root README): a distributed repository of declarative knowledge, focal deduction in perfect-information spaces, contribution to benign proliferation. That is enough to keep lower work from drifting into a generic theorem-prover or a generic RAG store.
- **Seminal constraints** are named (`tlph009`, `tlad005`): HOL/STT as the universal abstract representation; deduction in perfect-information spaces; focal methods rather than LLMs for those spaces.
- **Subsystem split** is stable and right (`tlad003`, root README): `kr`, `dk`, `di`, `mcp`, plus `docs`. Delivery to agentic clients via MCP, not a human UI, is already a design decision (`ampl001`).
- **KR prototype work is real.** `kr/` has abstract structure (`krcd006.sml`), native I/O (SML and Python), tests, and an architecture overview (`krad001.md`) that is more concrete than `docs/tlad012.md`. The onion strategy in `ampl001` (KR core, then kernel, then DI, MCP from the start) is still the right engineering order.
- **Recent philosophy work is the densest writing in `docs/`.** `tlph021` (history of deduction / Hilbert completeness thread) is a serious document. Supporting notes in `tlph002`, `tlph010`, `tlph013` were updated in the current working tree. Evolution material (`tlph022`–`tlph024`) exists as a third pillar beside synthetic philosophy and deductive engineering.

These strengths do not substitute for interface-level architecture.

## Gaps, ordered by effect on KR and MCP

### 1. `tlad012` is a heading list, not an interface

`docs/tlad012.md` enumerates: simple name, relative name, constraint, extension, theory, context, view, cache — then stops.

That list is the intended hinge between philosophy and implementation. Without definitions, operations, identities, and consistency rules, neither KR detailed design nor MCP tools can be derived from `docs/`.

Meanwhile `kr/krad001.md` already talks about hashes, types, terms, sequents, signatures, extensions, theories, folders, trees, local vs diasporic vs pansophic repositories, contexts and views. The two documents do not yet tell the same story in the same words.

**What to do first, and how**

Treat `tlad012` as the system-wide *abstract model*, and `krad001` / `krdd*` / `krcd*` as its KR-local elaboration — not as competing drafts.

For each object on the `tlad012` list, write (briefly, but completely enough to implement against):

- What it *is* (one paragraph, glossary-aligned).
- What operations create, combine, or query it.
- What is identity (name? hash? path?).
- What must be conserved (especially conservative extension).
- What a *view* or *cache* is allowed to drop or recompute.
- What the MCP server may expose in the first read-only prototype vs later.

Do not invent a second vocabulary. Reconcile with `krad001`. If `tlad012` says "cache" and `krad001` does not, either define it or drop it from the top-level list until it is needed.

A useful stopping test: an AI given only `tlad001`, `tlad003`, `tlad012`, and `krad001` could list MCP tools for "open repository, list contexts, get theory/extension, resolve name, fetch sequent" without guessing.

### 2. MCP is an implementation directory without a service specification

`mcp/README.md` lists Python files and tests. `tlad003` says the server gives agentic clients access to the repository and to reasoning. `ampl001` correctly wants a read-only MCP as soon as a stored repository exists.

There is no top-level document that says:

- which KR operations are tools in v0 (read-only);
- which are out of scope until a kernel exists;
- how a "context" is named on the wire;
- what error/empty/untrusted looks like;
- whether ProofPower/HOL4 helper MCP servers are in-tree or separate.

Without that, further MCP coding will encode whatever is convenient in `mcpcd001.py`, and the architecture will follow the prototype instead of governing it.

**What to do, and how**

Add a short architecture note (either a new `tlad` or a substantial section of `tlad012` plus a pointer from `mcp/README.md`) whose only job is the **v0 tool surface**:

- Inputs: a native repository (the linearised form already in view in `ampl001`).
- Tools: inspect metadata, list theories/contexts, retrieve a named object, perhaps dump a view.
- Explicit non-goals for v0: write, prove, train, marketplace, blockchain.

Keep it to a few pages. The existing `mcpte002.md` start-up notes are operational, not architectural.

### 3. Kernel and trust are sketched, not specified

`tlad013` and the kernel section of `tlad003` contain the important *policy* idea: not LCF ADT monopoly; theorems signed by authorities; views filtered by a lattice of trust (and later by secrecy). `tlad014` exists on cryptography.

That is not yet enough to design:

- the theorem object (sequent + context + signatures + trust expression);
- primitive HOL rules vs oracles vs derived rules as distinct authorities;
- how a signed theorem is stored in KR;
- what the kernel MCP tools would be (later than KR read-only).

**What to do, and how**

Do **not** start a full kernel implementation. Write one page of *invariants* into `tlad013` (or a `dk` architecture file that `tlad013` points to):

- A theorem is always relative to a context.
- Signature set is metadata, not a substitute for the sequent.
- Primitive kernel authority is one key among many.
- Views filter; they do not rewrite sequents.

Then stop until `tlad012` and v0 MCP are usable. Kernel work before a stable context/theory object will be wasted motion.

### 4. The path through the docs is not a path

`docs/README.md` lists ~25 philosophy files and 14 architecture files with almost no reading order. `tlpl001.md` is stale (it points "Synthetic Philosophy" at `tlph001` and "Deductive Engineering" at `tlph002`; those roles now sit on `tlph002` / `tlad007`). `tlph016.md` exists and is in `drafts/README.md` but not in `docs/README.md`. Several `tlph` files are under 20 lines (`tlph003`, `tlph004`, `tlph008`, `tlph011`, `tlph017`, `tlph019`, `tlph020`).

Duplication is already a tax: purpose appears in `tlph012`, `tlmc001`, `tlmc003`; rationale in `tlph014`, `tlad009`, `tlad011`; evolution in `tlph015` and `tlph022`–`tlph024`. That is acceptable while thinking, harmful when an AI must guess which file is canonical.

**What to do, and how**

Do not merge everything. Declare **canonical entry points** and treat the rest as supporting:

| Role | Canonical now | Supporting |
|---|---|---|
| Purpose | `tlph012` | `tlmc001`, `tlmc003` |
| Synthetic philosophy | `tlph002` | `tlph001`, `tlph006`, `tlph019` |
| Deductive engineering | `tlad007` | `tlph005`, `tlph018` |
| Architecture overview | `tlad003` | `tlad004`, `tlad002` |
| KR abstract model | `tlad012` | `krad001`, `krdd*`, `krph*` |
| Perfect information / focal | `tlad005` + `tlad008` | `tlph009` |
| Evolution / benign proliferation | `tlph022` (and 023–024 as they mature) | `tlph015`, `tlph001` |

Fix `tlpl001` or replace it with a short "how to read these docs" at the top of `docs/README.md`. Index `tlph016` or drop it from drafts. Mark stubs as stubs in the index so they are not mistaken for load-bearing text.

This is cheap and should happen in parallel with (1), not instead of it.

### 5. Philosophy that can wait for KR/MCP resumption

`tlph021` and the Hilbert/completeness thread are valuable and should stay in the tree. They are **not** the bottleneck for KR data structures or MCP tools.

The same is true of unfinished sections in `tlph021` (Carnap II, theory of computation, architectural implications) and of `tlph017`–`tlph020` stubs. Fill them when a KR question actually needs them (e.g. authority/skepticism when trust lattices are specified; metaphysics when "model" ambiguity in `tlad012` is resolved).

**Rule of thumb:** if a philosophy gap does not change the KR object model or the v0 MCP tool list, it is not first.

`tlad005` is Copilot-authored, dated, and longer than most human architecture notes. It is useful on PIS vs games vs theories. It should be treated as a *draft to be owned*, not as frozen spec, when it is next edited.

## Recommended sequence

This is a writing sequence, not a waterfall for the whole project. It matches `ampl001`'s onion (KR stored form → read-only MCP → kernel later) and `drafts/README.md`'s stated focus.

1. **Canonical map** (hours, not weeks): reading order on `docs/README.md`; fix `tlpl001` pointers; index or park `tlph016`; label stubs. Outcome: a new session can be told "read these six files."
2. **`tlad012` abstract model**, reconciled with `krad001` (the main writing). Outcome: named objects, operations, identity, conservative extension, view/cache. Outcome test: MCP v0 tool list can be written without new ontology.
3. **MCP v0 service note** (tools, non-goals, context naming). Then, and only then, MCP code changes are "implementation of the note."
4. **`tlad013` invariants** for theorem + signature + context, still short. No kernel coding required to resume KR.
5. **Philosophy on demand**, starting from questions raised by (2)–(4): additive knowledge and conservative extension (`tlph010`/`tlph013`/`tlph017`); authority (`tlph020`/`tlad014`); what "benign" constrains in the architecture (`tlph011`/`tlph012`).

Implementation already in `kr/` (native I/O, tests) should continue as the check that (2) is true of the code, not as a parallel undocumented design.

## Opinions on organisation (for the following discussion)

These are opinions, not already-decided policy.

- **Keep philosophy and architecture in `docs/`, subsystem design in `kr/`, `dk/`, `di/`, `mcp/`.** The failure mode is not the split; it is `tlad012` remaining empty while `krad001` and `krcd*` quietly become the real architecture.
- **`drafts/README.md` should not be a second index of living `docs/` files.** Once a document is linked from `docs/README.md`, drafts should say *what is unfinished in it*, not re-list it. Otherwise AI sessions start from the wrong catalogue.
- **Do not grow more `tlph` numbers until a gap in the canonical map demands a new file.** Several existing files are empty enough to absorb the next paragraphs.
- **Forward plan for implementation should stay in `docs/admin/ampl001.md` (or a successor),** not in `tlpl001.md`. `tlpl001` is about *documentation* strategy; `ampl001` is about *prototyping* strategy. They have been allowed to diverge. Align them in one paragraph each pointing at the other.
- **Agent instructions (`Agents.md`) are right for this phase:** discuss and assess; write reviews and `.grok/` only. When `tlad012` and the MCP note exist, the instruction should change to: implement against those two documents.
- **Worktrees / session isolation** (from earlier session notes) matter once docs and code move together; they do not fix the documentation gap.

## What this review is not

- It does not claim the philosophy is finished or should stop.
- It does not treat prototype `kr/`/`mcp/` code as wrong; it treats it as under-specified from above.
- It is not a request to Grok to edit `docs/` in this session.

## Suggested next conversation

Agree:

1. The canonical six (or so) files an AI must read.
2. Whether `tlad012` is the abstract model (recommended) or whether `krad001` should be promoted and `tlad012` reduced to a pointer.
3. The v0 MCP tool list, even as bullets.
4. What "done enough to resume KR/MCP" means in one sentence, so later reviews have a pass/fail test.
