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

The workflow is split into two explicit stages. Copilot executes Stage 1 and opens a draft pull request. Stage 2 happens only after the maintainer has reviewed and edited the Stage 1 artefacts.

### Stage 1 — Candidate Proposal (Draft PR)

1. **Establish baseline**
   - Locate the most recent glossary augmentation report (`reviews/YYYYMMDD-HHMM-*-glossary-augmentation.md`) and note the date for reference.
   - Optionally export the current glossary anchors for cross-checking with `python3 docs/admin/amcd002.py --output json > /tmp/glossary_terms.json`.

2. **Discover candidates with automation**
   - Run `python3 docs/admin/amcd003.py --output json --min-frequency 2 --min-files 2 > /tmp/glossary_candidates.json`.
   - Review the JSON and shortlist only project-relevant terms. Exclude existing glossary entries, generic vocabulary, and artefacts unique to tooling.

3. **Prepare the maintainer-facing candidate list**
   - Create `reviews/YYYYMMDD-HHMM-copilot-glossary-candidates.yaml` (use UTC timestamp).
   - Record one term per line in YAML sequence form for easy editing, e.g.:

     ```yaml
     candidates:
       - Knowledge Repository
       - Native Repository
       - Deductive Kernel
     ```

   - Keep the document limited to the proposed term names; omit tables, statistics, or inline commentary.

4. **Open a draft pull request**
   - Create a feature branch containing only the YAML candidate list (and any optional supporting notes).
   - Open a draft PR titled “Glossary candidates YYYY-MM-DD” and request maintainer review. No glossary edits are made at this stage.

5. **Await maintainer curation**
   - The maintainer may remove, reorder, or add terms directly in the YAML file. Copilot pauses here until explicit approval to proceed with Stage 2.

### Stage 2 — Glossary Integration (Maintainer Approved)

1. **Confirm scope**
   - Sync the branch with the maintainer’s revisions to the YAML list. Treat the edited list as the authoritative scope for the iteration.

2. **Draft glossary entries**
   - For each term, determine whether an existing document offers a canonical explanation. Capture the relative path and anchor if one exists.
   - Add entries to `docs/tlad001.md`, maintaining alphabetical order and letter headings. When a target section is missing, extend the index accordingly.
   - Follow the established entry pattern:

     ```markdown
     ### [Term Name](relative/path.md#anchor)

     Concise SPaDE-specific definition (expand in full when no external reference is available).
     ```

3. **Run incremental linking (amcd001.py)**
   - Execute `python3 docs/admin/amcd001.py --since <last-review-date>` or `--files …` to insert links pointing to the new glossary entries.
   - Ensure the glossary provides dedicated headings for any subtopics that should receive links (e.g. convert bulleted glosses into `####` subsections before running the script).
   - Review the diff for over-linking or unintended edits and adjust filters if needed.
   - Pay special attention to emphasised text: the script should treat emphasised spans as atomic; avoid linking single words inside highlighted phrases unless the whole span is the glossary term.
   - Links that would resolve to anchors within the same document should default back to the glossary entry; flag any self-links for manual review.

4. **Regenerate reports**
   - Produce an updated candidate summary if helpful (`amcd003.py --output json`) and archive any supporting artefacts under `/tmp` or the PR description.
   - Author the augmentation report described in [amtd003.md](amtd003.md) (filename `reviews/YYYYMMDD-HHMM-copilot-glossary-augmentation.md`). Reference the YAML candidate list and note any deviations.

5. **Finalize the pull request**
   - Include all Stage 2 changes (glossary edits, automated links, augmentation report) in the existing PR.
   - Provide a concise summary of actions taken and any follow-up required. Await maintainer review before merging.

6. **Post-merge follow-up**
   - After merge, archive or delete temporary analysis files. If additional linking is required, raise a new task referencing the augmentation report.

## See Also

- [docs/tlad001.md](../tlad001.md) - The SPaDE Glossary
- [docs/admin/amtd002.md](amtd002.md) - Incremental glossary linking task
- [docs/admin/amtd003.md](amtd003.md) - Glossary augmentation task description
- [docs/admin/amms006.md](amms006.md) - Glossary link maintenance
- [docs/admin/amms001.md](amms001.md) - Project structure and naming conventions
