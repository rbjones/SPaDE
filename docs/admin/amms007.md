# Glossary Augmentation Procedure

## Purpose

This document describes a method for systematically identifying new technical terms in the SPaDE project documentation that should be added to the glossary, and for integrating those terms into the glossary and linking them throughout the documentation.

## Scope

This procedure applies to all markdown (.md) files in the SPaDE repository, excluding:

- The `reviews/` directory
- The `retro/` directory
- The `tools/` directory
- Any directory whose name begins with `.`
- The glossary file itself (`docs/tlad001.md`)

## Procedure Overview

The workflow is split into two stages, with Stage 1 focusing on candidate proposal and Stage 2 on glossary integration.
In Stage 1, Copilot opens a draft pull request, which delivers a curated list of candidate terms for review.
The review may then lead to modifications of the candidate list.
Stage 2 then integrates the approved terms into the glossary, links them throughout the documentation and generates an augmentation report.
After a final review the results are merged into the main branch.

To assist in undertaking this procedure, several supporting scripts are provided in the `docs/admin/` directory as follows:

- `amcd001.py` — Incremental glossary linking script
- `amcd002.py` — Glossary term frequency and occurrence extractor
- `amcd003.py` — Glossary candidate identification script

### Stage 1 — Candidate Proposal (Draft PR)

1. **Establish baseline**
   - Locate the most recent glossary augmentation report (`reviews/YYYYMMDD-HHMM-*-glossary-augmentation.md`) and note the date for reference.
   - Optionally export the current glossary anchors for cross-checking with `python3 docs/admin/amcd002.py --output json > /tmp/glossary_terms.json`.

2. **Discover candidates with automation**
   - Run `python3 docs/admin/amcd003.py --output json --min-frequency 2 --min-files 2 > /tmp/glossary_candidates.json`.
   - Review the JSON and shortlist only project-relevant terms. Exclude existing glossary entries, generic vocabulary, and artefacts unique to tooling.

3. **Prepare candidate list for review**
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
   - Open a draft PR titled “Glossary candidates YYYY-MM-DD” and request maintainer review.
   No glossary edits are made at this stage.

5. **Await maintainer curation**
   - The reviewer may remove or add terms in the candidate list.
   Work pauses until approval is given to proceed with Stage 2.

### Stage 2 — Glossary Integration (Maintainer Approved)

1. **Confirm scope**
   - Sync the branch with the maintainer’s revisions to the YAML list. Treat the edited list as the authoritative scope for the iteration.

2. **Draft glossary entries**
   - For each term, determine whether an existing document offers a suitable explanation. Capture the relative path and anchor if one exists.
   - Add entries to `docs/tlad001.md`, maintaining alphabetical order and letter headings. When a target letter heading is missing, add the heading and extend the index accordingly.
   - Follow the established entry pattern:

     ```markdown
     ### [Term Name](relative/path.md#anchor)

     Concise SPaDE-specific definition (expand in full when no external reference is available).
     ```

3. **Run incremental linking (amcd001.py)**
   - Execute `python3 docs/admin/amcd001.py --since <last-review-date>` or `--files …` to insert links pointing to the new glossary entries.
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
