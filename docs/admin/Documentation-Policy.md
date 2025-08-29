# Project Structure and Documentation Policy

The project is organised into subsystems each with its own top-level directory, in addition to which there is a docs directory for materials not specific to any single subsystem.

The subsystems are at present:

- kr - Knowledge Repository
- dk - Deductive Kernel
- di - Deductive Intelligence

Where there is no compelling reason to do otherwise, documents will be written in github markdown, and will be organised in such a way as to provide a transparent and complete view of the project from the project web site on rbjones.github.io/SPaDE

## File Naming Convention

File names should be stable and descriptive (unless in a numeric sequence), independent of document titles:

- Use descriptive, stable names: `collaboration-framework.md`, `project-issues.md`
- No need to closely couple file names to document titles
- Maintain consistent naming patterns across directories
- Document titles can evolve without requiring file renames

## Documentation Organization

Documents specific to some subsystem will be in the top-level directory for that subsystem.

High level and project wide documentation will be in the [docs](../README.md) directory, which has an [admin](README.md) subdirectory for materials of a non-technical nature.

The docs directory also covers:

- **Philosophy/**Philosophical foundations and concepts
- **Architecture/**: System architecture and design
- **Specifications/**: Formal mathematical specifications relevant to multiple subsystems
- **Papers/**: Academic publications and formal papers

For low-level technical materials common to more than one subsystem, the top-level [common](../../common/) directory will be used.

For material of a non-technical nature there is an [admin](admin) subdirectory of the docs directory.

This includes:

- Overall project plans or development strategies and tactics
- Guidance for potential and actual collaborators, both human and AI, either in this project or in associated but distinct enterprises,including:

  - Identification of possible contributions, both in the core project and in separate repos.
  - Guidance on best practices for collaboration and communication.
  - Standards for documentation and code quality.

## Collaboration Documentation

- All collaboration methods and workflows are documented in `admin/`
- Human/AI collaboration framework is essential to project success
- Regular review and refinement of collaboration methods
- Clear roles and responsibilities for human and AI contributors

## Exceptions to Markdown Policy

The following are the exceptions to that policy which are currently anticipated:

### Conference Papers

There will be a small number of papers prepared as if for publication in the proceedings of conferences, in whatever the required format is (normally latex with a special formatting). Where possible these may be constructed using the markdown package to include markdown sources.

### ProofPower .pp Files

Historical material in the retro directory is mostly in .pp files, which are in a ProofPower literate script format normally including both tex source and formal specifications in HOL. These are intended ultimately both for processing by ProofPower and for creating PDF documents using texlive.

### Reference PDF

It is likely that a compendium of project documentation as a PDF reference manual will be desirable if the development is successful. This would likely be produced by texlive, mainly compounded from .md files incorporated using the markdown package or converted to .tex files using pandoc, with one or more .tex files glueing them together.

### Formal Specifications

These will form the main part of the technical output during the early stages of the project, and will be in ProofPower HOL. Provided that no insuperable technical obstacles appear, these specifications will be incorporated into .md files.

### Code Documentation

The reflexive nature of the project architecture means that from the earliest possible stage the abstract representation of algorithms will be in the HOL abstract syntax, and concrete syntax will be supplied as required by LLM like general intelligence in an outer shell. The implications of this for the documentation is not yet clear, but the preference will continue to be to address the needs through descriptions in github markdown documents. First prototyping of the logical kernel are likely to be by transcription from HOL to SML.

## Evolution

This policy will evolve as the project develops and we learn what works best for our collaboration and documentation needs. All changes should be documented and justified based on our experience.

---

*This policy is essential to maintaining transparency and accessibility throughout the project's development.*
