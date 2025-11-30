# Glossary Augmentation Report

**Date**: 2025-11-03
**Time (UTC)**: 15:22
**Author**: copilot

## Context

- **Source candidate list**: `reviews/20251103-1505-copilot-glossary-candidates.yaml` (temporary artefact removed after Stage 2 per maintainer preference)
- **Previous augmentation report**: none on record (prior run was reverted, see Stage 1 notes)

## Candidate Review

| Term | Status | Notes |
| ---- | ------ | ----- |
| Knowledge Repository | Added | Core concept described in `kr/krad001.md` outlining repository structure and provenance guarantees. |
| Deductive Kernel | Added | Summarised from `dk/README.md` to capture the inference engine responsibilities. |
| SPaDE Native Repository | Added | Definition anchored to `kr/krdd002.md` covering serialisation format. |
| Alonzo Church | Added | Standalone entry explaining the historical underpinning for the project’s logic. |
| Simple Theory of Types | Added | Clarifies the foundational logic adopted by SPaDE. |
| Deductive Intelligence | Added | Linked to `di/README.md` and positioned alongside Deductive Kernel. |

No candidates were deferred in this iteration.

## Glossary Updates

- Inserted new entries in `docs/tlad001.md`, adding a `K` section to accommodate “Knowledge Repository”.
- Added cross-references between the new terms to highlight their relationships (e.g. Deductive Kernel ↔ Knowledge Repository).
- Ensured alphabetical order and updated the letter index accordingly.

## Documentation Linking

Ran `docs/admin/amcd001.py` to refresh glossary links in key documents:

```bash
/Users/rbj/git/SPaDE/.venv/bin/python docs/admin/amcd001.py --files README.md docs/admin/ampl001.md docs/admin/ampl002.md docs/admin/amms001.md dk/README.md di/README.md docs/README.md docs/tlad003.md kr/krad001.md
```

Result: 52 links added across the processed files (breakdown recorded in terminal output).

## Follow-up

- Stage 1 candidate shortlist was a temporary artefact and has been removed; regenerate on the next iteration.
- Next scheduled maintenance task: continue incremental linking (`amtd002.md`) during the next documentation sweep or after further glossary additions.
- Open issues from maintainer review (2025-11-03 19:41 UTC):

    1. Pointing glossary links at intradocument anchors (e.g. `dk/README.md#overview`) is undesirable; scripts should target the glossary entry instead and flag self-links for manual handling.
    2. Do not auto-link single words inside emphasised multi-word phrases; treat emphasised spans as atomic and require explicit approval before linking.
    3. Glossary needs per-item anchors for the “Focal …” subentries; restructure the list under “Focal” into subheadings before enabling links.
    4. Review and fix existing erroneous glossary links (e.g. `di/README.md` pointing to `#deductive-intelligence-di-directory`).

- Planned remediation sequence:

  - Patch `amcd001.py` detection heuristics (respect emphasis, avoid self-links, warn on missing anchors).
  - Restructure `docs/tlad001.md#focal` with subheadings and rerun linking.
  - Manually audit the documents flagged in the review once the heuristics are updated.
