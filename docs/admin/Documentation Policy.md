Documentation Policy

Where there is no compelling reason to do otherwise, documents will be written in github markdown, and will be organised in such a way as to provide a transparent and complete view ot the project from the project web site on rbjones.github.io/SPaDE

The following are the exceptions to that policy which are currently anticipated:

* There will be a small number of papers prepare as if for publication in the proceedings of conferences, in whatever the required format is (normally latex with a special formatting).  Where possible these may be constructed using the markdown package to include markdown sources.

* ProofPower .pp files.
    Historical material in the retro directory is mostly in .pp files, which are in a ProofPower literate script format normally including both tex source and formal specifications in HOL.
    These are intended ultimately both for processing by ProofPower and for creating PDF documents using texlive.

* Reference PDF
    It is likely that a compendium of project documentation as a PDF reference manual will be desirable if the development is successful.
    This would likely be produced by texlive, mainly compounded from .md files incorporated using the markdown package or converted to .tex files using pandoc, with one or more .tex files glueing them together.

*   Formal specifications
    These will form the main part of the technical output during the early stages of the project, and will be in ProofPower HOL. Provided that no insuperacble technical obstacles appear, these specifications will be incorporated into .md files.

*   Code
    The reflexive nature of the project architecture means that from the earliest possible stage the abstract representation of algorithms will be in the HOL abstract syntax, and cocrete syntax will be supplied as required by LLM like general intelligence in an outer shell.
    The implications of this for the documentation is not yet clear, but the preference will continue to be to address the needs through descriptions in github markdown documents.
    First prototyping of the logical kernel are likely to be by transcription from HOL to SML.

    

