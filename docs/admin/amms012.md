# Method for Writing ProofPower HOL Specifications

This document outlines methods for writing formal specifications for the SPaDE project using ProofPower HOL.
It clarifies the intended role for such specifications, identifies the context in which those specification are to be written and seeks to provide the best possible links into the documentation with which agents must be familiar to undertake the specifications successfully.

It is presented in the following parts:

- [The Role of ProofPower HOL in the SPaDE development](#the-role-of-proofpower-hol-in-the-spade-development)
- [Context for Writing ProofPower HOL Specifications](#context-for-writing-proofpower-hol-specifications)
- [Links to Relevant Documentation](#links-to-relevant-documentation)

## The Role of ProofPower HOL in the SPaDE development

SPaDE is intended to be a reflexive project, rooted in essentially the same logical system as ProofPower HOL.
It is intended to support "deductive engineering" using reflexive methods as a service for LLMs using the MCP protocol.

The reflexive nature of the project requires that the specifications will in due course be held in SPaDE knowledge repositories, and that once sufficient capability is established further specifications and the deductive application of them will be managed within the SPaDE framework.

The specifications are of course needed before that functionality is in place, and to ensure the integrity and coherence of the specifications we need something to process them.
ProofPower HOL has been chosen to fulfill that role, which is part of a complex bootstrap operation necessary to get SPaDE off the ground.

## Context for Writing ProofPower HOL Specifications

The foundational logical system of SPaDE is substantially similar in the substance if not in form to that of ProofPower HOL.

The relevant context falls under the following headings:

- [Points of Divergence between ProofPower HOL and SPaDE](#points-of-divergence)
- [Documentation for ProofPower HOL](#documentation-for-proofpower-hol)
- [The Theory Heirarchy](#the-theory-heirarchy)

### Points of Divergence between ProofPower HOL and SPaDE

In writing the specifications it is necessary to be aware that the system we are trying to deliver is not the same as ProofPower HOL, even though the logical system is almost identical (as an abstraction).

There are three principle points of divergence.

The first, concerns the reflexive aspects of SPaDE, which demand a new inference rule which allows functions shown to be logically sound to be applied directly in deriving further conclusions within the system.
This intended to make no difference to the theorems which are provable, but simply to shorten proofs.

To make the reasoning about the deductive system efficient, the provision for literal constants is modified to provide convenient support for term literals via an encoding of abstract syntax into byte sequences.

The third point of divergence concerns the claim to universality for declarative languge of the HOL specification language.
The alleged unversality attaches not to the bare HOL logical system, but rather to something which SPaDE calls a "universal foundational institution".
This is not the place to explain that concept, but its consequence for the SPaDE logical system is a preference for strong infinity principles, effectively large cardinal axioms.
So the SPaDE variant of HOL will come with strong infinity axioms.

## Documentation for ProofPower HOL

There are multiple sources of documentation for ProofPower HOL, so I will provide references to the full range of available materials, together and also identify a compact subset which may be sufficient for most purposes.

The most comprehensive resource is the ProofPower repository at github.com/robarthn/pp.
The build of ProofPower creates the documentation as PDF files but for many purposes it may be more instructive to refer to source files.

The SPaDE development environment contains a close of the utf8 branch of the ProofPower repository, which has been built and therefore contains the executables and the PDF documentation.

The documentation is also available online at:

    https://www.lemma-one.com/ProofPower/doc/doc.html

Only a few of the ProofPower manuals are relevant to SPaDE.

The relevant documents are:

- [ProofPower - Description](https://www.lemma-one.com/ProofPower/doc/usr005.pdf). This manual provides an account of the concrete syntax of ProofPower HOL.  Note that there are two versions of ProoPower HOL available, the first of which uses a special 256-character set, and the second utf8.
SPaDE specifications are to be written for the utf8 version.
- [ProofPower HOL Reference Manual](https://www.lemma-one.com/ProofPower/doc/usr029.pdf)
This is a comprehensive reference both for the theories provided with ProofPower HOL and for the functions available (and other objects) in the SML meta-language for programming proofs and extending the functionality of the tool.
- [ProofPower - HOL Tutorial](https://www.lemma-one.com/ProofPower/doc/usr004.pdf)
- [ProofPower - HOL Tutorial](https://www.lemma-one.com/ProofPower/doc/usr004.pdf)
This described how to prepare ProofPower source material as literate scripts in LaTeX documents.
This is not in itself directly relevant to SPaDE which does not make use of this machinery, and is not intended to accept or deliver concrete syntax.
But it may be helpful if referring to PeoofPower source documents and for constructing specifications before SPaDE reaches it target modes of operation, at which stage, though SPaDE uses "SML" embedded in markdown, the SML is that augmented in ProofPower for the presentation of HOL paragraphs, which, until the specifications are transferred into a SPaDE native repo will remain the way in which HOL is used in practice for the development of SPaDE.

Note that the links above go to the lemma-one website and the documents are from the main branch of ProofPower not the utf8 branch, so its better to pick them up from the built utf8 branch clone available in the SPaDE development environment (at $PPDIR/bld/doc).

SPaDE uses a minimal part of the ProofPower HOL theory hierarchy in its specifications.
This is important to minimise the complexity of reflexive features of SPaDE.

The minimisation of such context is achieved by the use of the SPaDEroot theory (defined in [tlcd002.md](tlcd002.md)).
That theory is a child of the theory "basic_hol", so the context for the SPaDE specifications is the ancestry of basic_hol and the content of SPaDEroot.

It will therfore be helpful to agents contributing to the SPaDE specifications to look carefully at the ancestry of basic_hol and the content of SPaDEroot.

The ancestry of basic_hol is documented in the ProofPower HOL reference manual [usr029](https://www.lemma-one.com/ProofPower/doc/usr029.pdf).
A more compact rendition of the key theories may be found in HTML at :https://www.rbjones.com/rbjpub/pp/pptheories.html

It may however be instructive for agents seeking to contribute specifications to refer to the source file which create the theories. These source files are located in the `src` directory of the ProofPower repository.

The names of the relevant files are as follows:


| Theory name | Source files |
|--------------|-------------|
| min | imp006.pp |
| log, init, misc | dtd023.pp, imp023.pp |
| pair | dtd023.pp, imp023.pp |
| list | dtd039.pp, imp039.pp |
| char | dtd040.pp, imp040.pp |

