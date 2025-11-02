# Glossary Augmentation Procedure

## Purpose

This document describes the method for systematically identifying new technical terms in the SPaDE project documentation that should be added to the glossary.

## Scope

This procedure applies to all markdown (.md) files in the SPaDE repository, excluding:

- The `reviews/` directory
- The `retro/` directory  
- Any directory whose name begins with `.`
- The glossary file itself (`docs/tlad001.md`)

## Procedure Overview

### Step 1: Preparation

1. **Establish baseline**: identify the most recent glossary augmentation report (`reviews/YYYYMMDD-HHMM-*-glossary-augmentation.md`). Note that date for future reporting.
2. **Load current glossary terms**: run `python3 docs/admin/amcd002.py --output json > /tmp/glossary_terms.json` (optional but useful when cross-checking candidates). This script reflects the canonical list of headings and anchors in `docs/tlad001.md`.

### Step 2: Discover Candidate Terms (amcd003.py)

1. Execute `python3 docs/admin/amcd003.py --output markdown --min-frequency 2 --min-files 2 > reviews/latest-glossary-candidates.md`.
2. Review the generated candidate list. Each entry includes frequency, files, and example contexts to speed evaluation.
3. Remove obvious false positives (generic words, duplicates of existing glossary terms, concepts out of scope).

### Step 3: Evaluate Documentation Coverage

For each shortlisted candidate:

1. Use the file/line contexts in the amcd003 output to locate the authoritative explanation. Confirm it is stable, substantial, and appropriate to link.
2. If a strong explanation exists, record the document path and section anchor for reuse in the glossary heading.
3. If no adequate explanation exists, plan to provide a standalone definition within the glossary entry.

### Step 4: Draft Glossary Entries

1. Follow the established structure:

   ```markdown
   ### [Term Name](relative/path.md#anchor)

   Concise SPaDE-specific definition.

   Optional supporting paragraph(s) clarifying usage, relationships, or key attributes.
   ```

   Omit the link wrapper only when no authoritative source exists.

2. Maintain tone, formatting, and cross-linking conventions used elsewhere in `docs/tlad001.md`. Link related glossary terms inline where helpful.

### Step 5: Integrate Entries into the Glossary

1. Insert each new entry alphabetically within the appropriate letter section and update the letter index when introducing a new initial.
2. Re-run `python3 docs/admin/amcd002.py --output text` (optional) to spot-check that the new headings are parsed correctly and anchors resolve.
3. Save changes to `docs/tlad001.md` and prepare the augmentation report (see Deliverables in [amtd003.md](amtd003.md)).

### Step 6: Post-Augmentation Follow-up (amcd001.py)

1. Queue the incremental linking task ([amtd002.md](amtd002.md)). When ready, run `python3 docs/admin/amcd001.py --since <last-review-date>` or `--files <list>` to add links to the new terms across the documentation.
2. Capture the resulting glossary-link maintenance report produced by amcd001.py and store it in `reviews/` as part of the follow-up task.

## See Also

- [docs/tlad001.md](../tlad001.md) - The SPaDE Glossary
- [docs/admin/amtd002.md](amtd002.md) - Incremental glossary linking task
- [docs/admin/amtd003.md](amtd003.md) - Glossary augmentation task description
- [docs/admin/amms006.md](amms006.md) - Glossary link maintenance
- [docs/admin/amms001.md](amms001.md) - Project structure and naming conventions
