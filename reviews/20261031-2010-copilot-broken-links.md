# Broken-link audit

## Scope

This audit checks Markdown links in the repository after commit
`a1c4db8c035ccb5a62cfb5d0214e888f42217ad0` (31 October 2026). It checks
relative file targets and local Markdown anchors. External URLs and links in
historical review reports are excluded.

## Findings in files touched by the latest reorganisation

| File and line | Link | Finding |
| --- | --- | --- |
| [docs/admin/amtd000.md:26](../docs/admin/amtd000.md) | `#../tltd000.md` | The link uses `#` where `(...)` is required. It is interpreted as an anchor rather than a file link. |
| [docs/admin/amtd000.md:27](../docs/admin/amtd000.md) | `#../../kr/krtd000.md` | The link uses `#` where `(...)` is required. It is interpreted as an anchor rather than a file link. |
| [docs/admin/amtd000.md:28](../docs/admin/amtd000.md) | `#../../dk/dktd000.md` | The link uses `#` where `(...)` is required. It is interpreted as an anchor rather than a file link. |
| [docs/admin/amtd000.md:29](../docs/admin/amtd000.md) | `#../../di/ditd000.md` | The link uses `#` where `(...)` is required. It is interpreted as an anchor rather than a file link. |
| [docs/admin/amms001.md:55](../docs/admin/amms001.md) | `../docs/README.md` | From `docs/admin/`, this resolves to `docs/docs/README.md`. It should be `../README.md`. |
| [docs/admin/amms001.md:56](../docs/admin/amms001.md) | `../docs/admin/README.md` | From `docs/admin/`, this resolves to `docs/docs/admin/README.md`. It should be `README.md`. |
| [docs/admin/amms001.md:57](../docs/admin/amms001.md) | `../kr/README.md`, `../mcp/README.md`, `../dk/README.md`, `../di/README.md` | From `docs/admin/`, these resolve below `docs/`. They should use `../../kr/README.md`, `../../mcp/README.md`, `../../dk/README.md`, and `../../di/README.md`. |
| [docs/admin/ampd004.md:56](../docs/admin/ampd004.md) | `amtd007.md` | No `docs/admin/amtd007.md` exists. Either add the task document or change the reference to the document that defines the branch/worktree procedure. |

The new files [in/README.md](../in/README.md) and
[out/README.md](../out/README.md) contain no broken relative links. The
administrative index links added in the latest commit resolve correctly.
Some of the issues above predate the latest commit but are in files that it
touched; the audit does not attribute those pre-existing errors to the
reorganisation.

## Earlier baseline findings

These are not caused by the latest commit but remain broken in the current
repository:

| File and line | Link | Finding |
| --- | --- | --- |
| [docs/tltd001.md:39](../docs/tltd001.md) | `../../kr/krdd004.md` | From `docs/`, this resolves outside the repository. It should be `../kr/krdd004.md`. |
| [docs/tltd001.md:43](../docs/tltd001.md) | `../../kr/krdd004.md#encoding-and-decoding-ntbs-and-related-data-types` | Same incorrect path, with an anchor. |
| [docs/tlcd004.md:28](../docs/tlcd004.md) | `#induction-over-t-expressions` | The heading is “Induction and Recursion over T-expressions”, whose generated anchor is `#induction-and-recursion-over-t-expressions`. |

There are also older glossary references to anchors such as
`#focal-engineering` and `#deductive-intelligence` that do not correspond to
headings in [docs/tlad001.md](../docs/tlad001.md). They should be reviewed
separately because they predate the latest reorganisation and may reflect
glossary terminology that has not yet been normalised.

## Result

The repository is not currently free of broken links. The files touched by
the latest commit contain the eleven issues listed under “Findings in files
touched by the latest reorganisation”; some of those issues predate the
commit. The three specific baseline issues and the glossary-anchor family
should be handled separately.
