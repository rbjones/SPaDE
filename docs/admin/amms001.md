# Project Structure and Documentation Policy

The project is organised into subsystems each with its own top-level directory.
A top-level docs directory provides materials not specific to any single subsystem, which includes the important philosophical side to the project and materials relating to the overall architecture and design of the system as a whole.
The docs directory also has an admin subdirectory for materials of a non-technical nature, including project management and collaboration policies and procedures, and guidance for potential contributors.

## Documentation

Where there is no compelling reason to do otherwise, documents will be written in github markdown, and will be organised in such a way as to provide a transparent and complete view of the project from the project web site on [rbjones.github.io/SPaDE](https://rbjones.github.io/SPaDE)
Formal materials where appropriate may be presented in markdown as literate scripts.

### Where a document lives

The SPaDE documentation mostly falls into the following categories:

1. Philosophical and Architectural materials in the [docs](../docs/README.md) directory.
2. Adminstrative documentation including standards and procedures in the [docs/admin](../docs/admin/README.md) directory.
3. Subsystem-specific implementation and design materials in their respective top-level directories (e.g., knowledge repository ([kr](../kr/README.md)), mcp server ([mcp](../mcp/README.md)), deductive kernel ([dk](../dk/README.md)), deductive intelligence ([di](../di/README.md)).

## File Naming Conventions

The general policy on naming of documents is that they should be in numerical series prefixed by short identifiers for the subsystem or subdirectory, and for the kind of document as follows.
This seems to be morphing to using the subsystem codes for directories, whether or not they are subsystems, so that the README.doc indexes all the documents with the same subsystem code.

This needs to be made sufficiently systematic for all contributors (including copilot) to be able to choose filenames and maintain README.md files consistently.

### Ordering in README indexes

Within each document-type group, README.md entries should normally be kept in numerical order by document number, with the lowest numbered document first. This is the default convention for admin, subsystem, and top-level documentation indexes because it makes browsing, diff review, and later automation easier. The numbering convention is therefore more than cosmetic: it provides a stable, predictable ordering that contributors and agents can rely on when scanning the project or adding new documents.

Where a document is current or historical, the status should be recorded in the short description, but the ordering should remain numerical. This is preferred to reordering by status, chronology, or perceived urgency, because those are less stable and can create avoidable churn in the documentation.

### README completeness and historical status

A README.md for a directory should list every document in that directory that still exists. An entry should be removed only when the underlying file is deleted. This preserves a complete index and makes it clear when project documentation is being kept intentionally, not merely forgotten.

When a document is retained for historical interest but is not part of the current working baseline, it may be marked with a strikethrough while keeping the link active, for example: `~~amms007.md~~` or `~~[amms007.md](amms007.md)~~`. In Markdown, strikethrough is written as `~~text~~`, and it can be applied to the label while leaving the link itself live. This is a concise way to indicate that a document remains available for reference without implying that it is the current operating standard.

### Avoiding time-sensitive procedural commentary

Current procedure documents should describe enduring policy and working methods, not time-sensitive commentary about the state of tools, product changes, or temporary debates. Explanations of why a particular tool or workflow was being evaluated, or material that depends on a short-lived product state, belong in change histories, review reports, or chat logs rather than in the standards themselves.

In other words: the standard should record the endpoint, not the temporary path. The substantive content of a procedure should remain readable as a stable instruction, while the historical narrative belongs elsewhere.

Subsystem codes:

- **am** docs/admin - administration and management
- **co** common -low level common materials
- **di** di - deductive intelligence
- **dk** dk - deductive kernel
- **gh** .github - github workflows and actions etc.
- **kr** kr - knowledge repository
- **mcp** mcp - MCP server and A2A protocol
- **rv** reviews - review reports e.g. from copilot
  - **Exception**: Review files in the reviews directory use temporal naming: `YYYYMMDD-HHMM-author-topic.md`, see [reviews](./#reviews).
- **tl** tl - top level, system wide.  This includes files in the docs directory but not those in the admin subdirectory. The documentation at this level should all be in the docs directory rather than the top level directory, and mainly consists of high level system wide philosophy and architecture documents.

Document kinds:

- **ph** Philosophical materials
- **ad** Architectural level design
- **hd** High level design
- **dd** Detailed design
- **cd** Detailed formal specifications and code
- **ci** Continuous integration, release and deployment
- **cl** Chat logs and conversation transcripts
- **mc** Miscellanea
- **ms** Methods and standards
- **pd** Process or procedure descriptions
- **pl** Plans and strategies
- **td** Task descriptions
- **te** Testing and evaluation
- **ep** Papers intended for external publication

After the two prefixes documents will have a three digit number starting at 001 for each kind of document.
This completes the basename.
Document name extensions will generally indicate the language in which the document is written, or the coding format.
In some cases documents will have derivatives whose filename has the same basename but a distinct extension.
This will happen when code or formal specifications are included alongside explanatory text in an .md file, or when the processing of one kind of formal text yields some other file (e.g. compiling a source module into an object module).
Except in such cases of derivative documents, basenames should be unique.
Derivative files having the same basename but a distinct extension should not be linked to separately in the README.md of the their directory.

## Document Headers and Footers

Document headers should be avoided in markdown pages because of the impact on web page readability and presentation.  A footer is more acceptable.
Dates need not be included, history can be traced through git logs.  The primary author should be indicated, which in the case of copilot should include the model name.  Where a document results from conversation with an AI agent a link to the chat log should be included.

In the case of code or formal specifications not embedded in markdown a brief header mentioning authorship, including model name if AI.

## The Admin Directory

This includes:

- Overall project plans or development strategies and tactics
- Guidance for potential and actual collaborators, both human and AI, either in this project or in associated but distinct enterprises,including:

  - Identification of possible contributions, both in the core project and in separate repos.
  - Guidance on best practices for collaboration and communication.
  - Standards for documentation and code quality.

## Collaboration Documentation

- All collaboration methods and workflows are documented in `admin/` (apart from one in the .github directory)
- Human/AI collaboration framework is essential to project success
- Regular review and refinement of collaboration methods
- Discussions preparatory to high-level documentation (e.g. philosophy and architecture) may be recorded in chat logs in the `admin/` directory and will be referred to in the relevant high-level documents
- Clear roles and responsibilities for human and AI contributors

## Exceptions to Markdown Policy

There was previously an intention to use markdown more exclusively, as in a literate script system, including for formal specifications or code, and at that time the following exceptions were noted.
The following exceptions to the policy were then noted, but probably are no longer relevant, insofar as there is no longer an intention to use markdown as a literate programming system.

### Conference Papers

There may be a small number of papers prepared as if for publication in the proceedings of conferences, in whatever the required format is (normally latex with a special formatting). Where possible these may be constructed using the markdown package to include markdown sources.

### ProofPower .pp Files

Historical material in the retro directory is mostly in .pp files, which are in a ProofPower literate script format normally including both tex source and formal specifications in HOL. These are intended ultimately both for processing by ProofPower and for creating PDF documents using texlive.

### Reference PDF

It is likely that a compendium of project documentation as a PDF reference manual will be desirable if the development is successful. This would likely be produced by texlive, mainly compounded from .md files incorporated using the markdown package or converted to .tex files using pandoc, with one or more .tex files glueing them together.

### Formal Specifications

These will form the main part of the technical output during the early stages of the project, and will be in ProofPower HOL. They will normally be in literate scripts either as .pp files or as .md files.

It is policy to progress all informal documentation into formal models at all levels.
At the lower levels this is part of the reflexive reasoning required to approach the first singular foci and is therefore of high priority.  At the higher levels it is probably less urgent.

### Code Documentation

The reflexive nature of the project architecture means that from the earliest possible stage the abstract representation of algorithms will be in the HOL abstract syntax, and concrete syntax will be supplied as required by LLM like general intelligence in an outer shell. The implications of this for the documentation is not yet clear, but the preference will continue to be to address the needs through descriptions in github markdown documents. First prototyping of the logical kernel are likely to be by transcription from HOL to SML.

## Reviews

When undertaking reviews, please place outputs from the review in a markdown file in the "reviews" directory file in the root of the repository, or in a subdirectory of that directory if the comments relate to a specific subproject.
Use a filename which includes the date and time of the review followed by the contributor name, (e.g. copilot).
The date and time should be rendered in a formal which collates the files in temporal order in a directory listing, e.g. 20241001-1530-copilot.md for a review made on 1st October 2024 at 15:30 by copilot.
A further component of the filename may be a brief indication of the subject matter, e.g. 20241001-1530-copilot-KRreview.md
Avoid using colons (:) in filenames as they cause issues with Jekyll/GitHub Pages processing.

## Evolution

This policy will evolve as the project develops and we learn what works best for our collaboration and documentation needs. All changes should be documented and justified based on our experience.
