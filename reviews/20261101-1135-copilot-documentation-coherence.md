# Documentation coherence review

## Scope

This review checks the documentation after commit
`8a9453c608a026e833eb5724675f889149419670`, following the broken-link audit
in [20261031-2010-copilot-broken-links.md](20261031-2010-copilot-broken-links.md).
It also considers whether the recent task, role, and worktree policy has been
propagated consistently through the documentation.

## Broken-link follow-up

The latest commit fixed the malformed links in `amtd000`, the incorrect
relative links in `amms001`, the two `tltd001` paths, and the outdated
`tlcd004` anchor. It also replaced the missing `amtd007` reference in
`ampd004`.

One issue from the previous audit remains:

- [docs/admin/amtd000.md](../docs/admin/amtd000.md) links to
  `../../kr/krtd000.md`, but the new file is at the repository root as
  [krtd000.md](../krtd000.md). The link should either be changed to
  `../../krtd000.md` or the document should be moved into `kr/`.

The live-document link check now reports 19 issues, down from 43. The
remaining issues include stale glossary anchors, references to absent
historical or planned source files, placeholder links (`...` and
`./AI.wiki`), and the one meta-task link above. The link checker does not
judge whether a reference to a planned file is intentional.

## Most significant coherence defects

### 1. The meta-task hierarchy has no stable placement rule

[amtd000.md](../docs/admin/amtd000.md) says that subsystem meta-tasks belong
in their subsystem directories and are numbered zero, but `krtd000.md` is at
the repository root while `tltd000.md`, `dktd000.md`, and `ditd000.md` are in
different locations. The administrative index does not list `amtd000.md`, and
the `kr/` index does not list the root-level `krtd000.md`.

The documentation needs one rule for the location and identifier of every
meta-task, followed by a consistent relocation or indexing pass. The current
state makes the hierarchy difficult for an agent to discover mechanically.

### 2. The set of top-level areas is incomplete

[amtd000.md](../docs/admin/amtd000.md) lists Philosophy and Architecture,
Knowledge Representation, Deductive Kernel, and Deductive Intelligence, but
does not list the MCP subsystem, despite [amms009.md](../docs/admin/amms009.md)
identifying four subsystems including MCP. It also does not give a task
hierarchy for the new `in/` and `out/` areas, although the root project now
documents both as project directories.

Either these areas need meta-tasks, or `amtd000` should explicitly state that
they are excluded from the current task hierarchy and identify who governs
them.

### 3. Task mechanics and task hierarchy are not fully reconciled

[ampd004.md](../docs/admin/ampd004.md) says a task branch is cut from `main`,
but later says a pull request may target a parent branch. It also says the
worktree is removed when the task pull request is finished, while the
hierarchical task model implies that a child task may need to remain available
until its parent integrates it.

The document should state whether:

- every task branch is cut from `main`, or a child is cut from its parent;
- a child pull request targets its parent branch or `main`;
- branch and worktree lifetime ends at child review, parent integration, or
  final merge.

Without those choices, the new hierarchy is descriptive rather than
operational.

### 4. The authoritative-document relationship is implicit

[amms009.md](../docs/admin/amms009.md) is now the current role model, and
[ampd009.md](../docs/admin/ampd009.md) and [ampd004.md](../docs/admin/ampd004.md)
define commissioning and worktree mechanics. Older documents such as
[amms002.md](../docs/admin/amms002.md) are marked as earlier positions, but
the indexes do not identify which documents are normative, historical, or
superseded.

An agent following the index can therefore encounter multiple apparently
valid procedures. The admin index should distinguish current standards and
procedures from historical or provisional material, or each superseded
document should point explicitly to its replacement.

### 5. The documentation indexes lag the new structure

[docs/admin/README.md](../docs/admin/README.md) lists `amms013.md`,
`amtd006.md`, and `amcd004.py`, but not the new `amtd000.md`. The root
[docs/README.md](../docs/README.md) does not expose the new administrative
meta-task, and [kr/README.md](../kr/README.md) does not expose `krtd000.md`
or the new task-hierarchy role it represents.

Because the project explicitly treats README files as complete directory
indexes, these omissions are structural defects rather than cosmetic issues.

## Recommended order of repair

1. Decide and document the canonical placement and parentage of meta-tasks.
2. Resolve the remaining `krtd000.md` location/link mismatch and index every
   meta-task.
3. Decide the branch, pull-request, and worktree lifetime rules for child
   tasks, then align `ampd004`, `ampd009`, and `ampd010`.
4. Classify current versus historical administrative documents in the admin
   index.
5. Add or explicitly exclude MCP, onboarding, and outreach from the meta-task
   hierarchy.
6. Clean the remaining glossary anchors and planned-file references.

No project files other than this review report and its index entry were
changed.
