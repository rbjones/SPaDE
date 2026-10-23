# Procedure for Writing Specifications in ProofPower HOL

## Introduction

There are two documents currently which overlap in this area and need to be sorted out.
This document should be procedural in nature, providing step-by-step guidance for writing specifications in ProofPower HOL.
The other [document](amms012.md) is intended to supply technical background necessary for this kind of work, mostly by reference to exiting documentation for ProofPower HOL.
So, expect that kind of material to be removed from this document as it is refined.

This document is intermediate between the general procedure for task assignment documented in amtd011.md and the specific task descriptions which call for writing specifications in ProofPower HOL, providing those aspects of such a task description which are common to all tasks involving the creation or modification of ProofPower HOL specifications.

The content consists of:

- [Documentation for ProofPower HOL](amms012.md#documentation-for-proofpower-hol)
- [ProofPower HOL in Markdown](#proofpower-hol-in-markdown)
- [Document and Theory Naming Conventions](#document-and-theory-naming-conventions)

## Documentation for ProofPower HOL

It is likely that it will be advantageous to provide special extracts of the ProofPower documentation focussing on those aspects which are needed for the specification work required in SPaDE, but this has not yet been done and so a selection of the existing documents is cited here pro-tem.
It may be that an early task will involve creating such extracts, which can then be referenced in subsequent tasks.

The documentation for ProofPower HOL may be found at $PPDIR/bld/doc as PDF files, or at [https://www.lemma-one.com/ProofPower/doc/doc.html](https://www.lemma-one.com/ProofPower/doc/doc.html).
The following documents are particularly relevant when writing specifications in HOL to be processed by ProofPower:

- [usr001.pdf]($PPDIR/bld/doc/usr001.pdf) - ProofPower - Document preparation
- [usr004.pdf]($PPDIR/bld/doc/usr004.pdf) - ProofPower - Tutorial Manual
- [usr005.pdf]($PPDIR/bld/doc/usr005.pdf) - ProofPower - Description
- [usr013.pdf]($PPDIR/bld/doc/usr013.pdf) - ProofPower - HOL Tutorial Notes
- [usr029.pdf]($PPDIR/bld/doc/usr029.pdf) - ProofPower - HOL Reference Manual

The following formal specifications of ProofPower HOL and the HOL proof system are particularly relevant since some of these specifications will be rewritten for SPaDE, with the intention that there is no substantive change to the deductive system.

There is also a philosophical narrative (in SPaDE's [Synthetic Philosophy](../tlad001.md#synthetic-philosophy) concerning the universality of a foundational institution closely related to this logical system the precise formal articulation of which will involve an account of the semantics.

- [spc001.pdf]($PPDIR/bld/doc/spc001.pdf) - HOL Formalised: Language and Overview
- [spc002.pdf]($PPDIR/bld/doc/spc002.pdf) - HOL Formalised: Semantics
- [spc003.pdf]($PPDIR/bld/doc/spc003.pdf) - HOL Formalised: Deductive System
- [spc004.pdf]($PPDIR/bld/doc/spc004.pdf) - HOL Formalised: Proof Development System
- [spc005.pdf]($PPDIR/bld/doc/spc005.pdf) - HOL Formalised: Formal Design of the Logical Kernel



In writing ProofPower HOL specifications for SPaDE, or in reading specifications prepared by others, it is important to be familiar with the relevant documentation listed above.

## ProofPower HOL in Markdown

ProofPower HOL specifications are normally prepared as literate scripts consisting of LaTeX documents with formal material embedded in the document in a form suitable for stripping into SML files for input to ProofPower HOL, which is an interactive program, interaction with which is conducted in the SML functional programming language.

The capabilities of SPaDE will not be delivered in the same way, since SPaDE is intended as a tool for use by LLMs via the MCP interface.
Nevertheless, formal specification is an important part in the development of SPaDE, and prior to the existence of the SPaDE system we need a way to present and check the specifications.
There is also for SPaDE a very special extra requirement that formal specification will play, since SPaDE is intended *ab initio* as a *reflexive* system, i.e. one which uses formal reasoning to establish derived inference rules which then provide more efficient ways of conducting further formal reasoning.

SPaDE documentation is primarily in github markdown, automatically transformed into HTML for web presentation.
Formal specifications used in the development of SPaDE are also primarily in markdown, with the formal material included in appropriately marked sections suitable for extraction and processing by ProofPower system.

Therefore, whereas in ProofPower LaTeX formal materials are introduced either with "=SML" or by a line beginning with a special reserved codeword, in SPaDE markdown all formal material are preceded by "```sml" and followed by "```" to denote code blocks.
The code block should include any special keywords used in corresponding ProofPower LaTeX, but not any "=SML".

Thus the paragraph:

```
    =SML
    new_SPaDE_theory ("my_theory", "SPaDEroot",[]);
    =TEX
```

in a LaTeX document, would be rendered:

```
    ```sml
    new_SPaDE_theory ("my_theory", "SPaDEroot",[]);
    ```
```

in markdown.

and
```
    @HOLCONST
    |   empty_list: 'a list'
    =TEX
```

in LaTeX Would be rendered:

```
    ```sml
    ⓈHOLCONST
    │   empty_list: 'a list'
    ```
```
in markdown.

## Theory names and listings

A theory name is brief and suggestive of the nature or role of the theory. Correspondence with the name of the document is not required. One document may create more than one theory.

The task description states each theory name and the names of its parent theories.

A theory is opened with `new_SPaDE_theory`, defined in [tlcd002.md](../tlcd002.md). The call names the theory, its parent, and any further parents. The procedure removes any previous version of the theory before creating it, so a repeated check succeeds whether or not the theory is already present.

The makefile in the document's directory records which document creates which theory. Each theory listing depends on the load of the document that creates that theory. The arrangement is the one in [retro/np/rbj.mkf](../../retro/np/rbj.mkf), where the listing of a theory depends on the `.ldd` of its document. A listing is produced for every theory. The use of the listings is not settled. The preference is to render each listing as a markdown document for the project web site.

The author of the specification adds the document to that makefile, so that the document is loaded and its theory listings are produced.
