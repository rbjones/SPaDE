# LLM Wiki

This is a document in progress inspired by the idea of getting AI to build its own wiki to maintain a contuous contribution to the project.
An exemplar was taken as a basis, but the requirement for SPaDE is far removed from the need which inspired the example, and the transformation is as yet very incomplete.
It is also necessary to reconcile this approach with the prior approach to exploiting AI, documente primarily in the other documents in the ammsxxx.md  series.

-----

A knowledge base maintained by Claude Code or other AIs concerning the SPaDE project to facilitate AI contributions to the SPaDE project.

At present this document is still in progress and should not be taken seriously, since it is in transformation from a very different application.

## Purpose

This wiki is intended to enable AI to contribute to the SPaDE project.
The purpose of the SPaDE project is to contribute to the proliferation of benign intelligence across the cosmos.
Further detail of that purpose is available in the repository.
Its refinement and documentation is part of the work involved in the project to which the AI is to contribute.

## Folder structure

The SPaDE project resides in a git repo hosted at github.
It will also develop one or more SPaDE repos which contain formal declarative language, and as much as possible of the narrative descriptions in the SPaDE git repo will eventually be formalised in such a SPaDE repo.
The SPaDE repo will be organised heirarchically into folders and theories, but this structure is not yet established.

The folder structure of the SPaDE git repo (of which this is a part) is documented in README.md files in each folder.
One top level directory [SPaDE/ai.wiki](./AI.wiki) is to be used by the AI for its own notes.

## Ingest Repository

Input will be in the form of pull requests and repository commits.

When the user adds a new source to `raw/` and asks you to ingest it:
﻿
1. Read the full source document
2. Discuss key takeaways with the user before writing anything
3. Create a summary page in `wiki/` named after the source
4. Create or update concept pages for each major idea or entity
5. Add wiki-links ([[page-name]]) to connect related pages
6. Update `wiki/index.md` with new pages and one-line descriptions
7. Append an entry to `wiki/log.md` with the date, source name, and what changed
﻿
A single source may touch 10-15 wiki pages. That is normal.
﻿
## Page format

Every wiki page should follow this structure:

```markdown
# Page Title

## Introduction

An introduction and overview of the topic covered by this page with links to the top-level sections.


﻿
**Last updated**: Date of most recent update.
﻿
---
﻿
Main content goes here. Use clear headings and short paragraphs.
﻿
Link to related concepts using [[wiki-links]] throughout the text.
﻿
## Related pages
﻿
- [[related-concept-1]]
- [[related-concept-2]]
```
﻿
## Citation rules
﻿
- Every factual claim should reference its source file
- Use the format (source: filename.pdf) after the claim
- If two sources disagree, note the contradiction explicitly
- If a claim has no source, mark it as needing verification
﻿
## Question answering
﻿
When the user asks a question:
﻿
1. Read `wiki/index.md` first to find relevant pages
2. Read those pages and synthesize an answer
3. Cite specific wiki pages in your response
4. If the answer is not in the wiki, say so clearly
5. If the answer is valuable, offer to save it as a new wiki page
﻿
Good answers should be filed back into the wiki so they compound over time.
﻿
## Lint
﻿
When the user asks you to lint or audit the wiki:
﻿
- Check for contradictions between pages
- Find orphan pages (no inbound links from other pages)
- Identify concepts mentioned in pages that lack their own page
- Flag claims that may be outdated based on newer sources
- Check that all pages follow the page format above
- Report findings as a numbered list with suggested fixes
﻿
## Rules
﻿
- Always update `wiki/index.md` and `wiki/log.md` after changes
- Keep page names lowercase with hyphens (e.g. `machine-learning.md`)
- Write in clear, plain language
- When uncertain about how to categorize something, ask the user
