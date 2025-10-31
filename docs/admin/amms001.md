# Project Structure and Documentation Policy

The project is organised into subsystems each with its own top-level directory, in addition to which there is a docs directory for materials not specific to any single subsystem.

## Documentation

Where there is no compelling reason to do otherwise, documents will be written in github markdown, and will be organised in such a way as to provide a transparent and complete view of the project from the project web site on rbjones.github.io/[SPaDE](../tlad001.md#spade)

Documents specific to some subsystem will be in the top-level directory for that subsystem.

High level and project wide documentation will be in the [docs](../README.md) directory, which has an [admin](README.md) subdirectory for materials of a non-technical nature.

## File Naming Convention

The general policy on naming of documents is that they should be in numerical series prefixed by short identifiers for the subsystem or subdirectory, and for the kind of document as follows.
This seems to be morphing to using the subsystem codes for directories, whether or not they are subsystems, so that the README.doc indexes all the documents with the same subsystem code.

This needs to be made sufficiently systematic for all contributors (including copilot) to be able to choose filenames and maintain README.md files consistently.

Subsystem codes:

- **am** docs/admin - administration and management
- **co** common -low level common materials
- **di** di - deductive intelligence
- **dk** dk - deductive kernel
- **do** docs - philosophy and architecture
- **gh** .github - github workflows and actions etc.
- **kr** kr - knowledge repository
- **mcp** mcp - MCP server and A2A protocol
- **rv** reviews - review reports e.g. from copilot
  - **Exception**: Review files use temporal naming: `YYYYMMDD-HHMM-author-topic.md`
- **tl** ? - top level, system wide (may be phased out)

Document kinds:

- **ph** Philosophical materials
- **ad** Architectural level design
- **hd** High level design
- **dd** Detailed design
- **cd** Detailed formal specifications and code
- **ci** Continuous integration, release and deployment
- **ms** Methods and standards
- **pl** Plans and strategies
- **td** Task descriptions
- **pd** Process or procedure descriptions
- **te** Testing and evaluation
- **ep** Papers intended for external publication

After the two prefixes documents will have a three digit number starting at 001 for each kind of document.
Document suffixes will generally indicate the language in which the document is written.

When undertaking reviews, please place outputs from the review in a markdown file in the "reviews" directory file in the root of the repository, or in a subdirectory of that directory if the comments relate to a specific subproject.
Use a filename which includes the date and time of the review followed by the contributor name, (e.g. copilot).
The date and time should be rendered in a formal which collates the files in temporal order in a directory listing, e.g. 20241001-1530-copilot.md for a review made on 1st October 2024 at 15:30 by copilot.
A further component of the filename may be a brief indication of the subject matter, e.g. 20241001-1530-copilot-KRreview.md
Avoid using colons (:) in filenames as they cause issues with Jekyll/GitHub Pages processing.

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

These will form the main part of the technical output during the early stages of the project, and will be in ProofPower HOL. Provided that no insuperable technical obstacles appear, these specifications will be incorporated into .md files.

### Code Documentation

The reflexive nature of the project architecture means that from the earliest possible stage the abstract representation of algorithms will be in the HOL abstract syntax, and concrete syntax will be supplied as required by LLM like general intelligence in an outer shell. The implications of this for the documentation is not yet clear, but the preference will continue to be to address the needs through descriptions in github markdown documents. First prototyping of the logical kernel are likely to be by transcription from HOL to SML.

## Reviews

- Reviews of documents and code are to be placed in the reviews directory with filenames indicating date, time, reviewer and subject.

## Evolution

This policy will evolve as the project develops and we learn what works best for our collaboration and documentation needs. All changes should be documented and justified based on our experience.
