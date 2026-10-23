# Method for Writing ProofPower HOL Specifications

This document outlines methods for writing formal specifications for the SPaDE project using ProofPower HOL.
It clarifies the intended role for such specifications, identifies the context in which those specifications are to be written and seeks to provide the best possible links into the documentation with which agents must be familiar to undertake the specifications successfully.

It is presented in the following parts:

- [The Role of ProofPower HOL in the SPaDE development](#the-role-of-proofpower-hol-in-the-spade-development)
- [Writing a specification](#writing-a-specification)
- [Context for Writing ProofPower HOL Specifications](#context-for-writing-proofpower-hol-specifications)
- [Links to Relevant Documentation](#links-to-relevant-documentation)
- [Supplementary Notes](#supplementary-notes)

## The Role of ProofPower HOL in the SPaDE development

SPaDE is intended to be a reflexive project, rooted in essentially the same logical system as ProofPower HOL.
It is intended to support "deductive engineering" using reflexive methods as a service for LLMs using the MCP protocol.

The reflexive nature of the project requires that the specifications will in due course be held in SPaDE knowledge repositories, and that once sufficient capability is established further specifications and the deductive application of them will be managed within the SPaDE framework.

The specifications are of course needed before that functionality is in place, and to ensure the integrity and coherence of the specifications we need something to process them.
ProofPower HOL has been chosen to fulfill that role, which is part of a complex bootstrap operation necessary to get SPaDE off the ground.

## Writing a specification

A SPaDE specification is a markdown document. The formal text is in `sml` fences. [tlci001.mkf](../tlci001.mkf) strips those fences with [rules.mkf](../../common/rules.mkf) and loads the script with ProofPower. ProofPower checks that the script is well-formed. It is not part of the deliverable. Whether the specification says what was wanted is a further check. Until SPaDE can check its own HOL, this load is the check. The image `ghcr.io/rbjones/pp/proofpower_arm` is available where ProofPower is not installed on the host.

A theory is opened with `new_SPaDE_theory`, defined in [tlcd002.md](../tlcd002.md):

```sml
new_SPaDE_theory ("theory_name", "parent", []);
```

The procedure opens the parent, removes any previous version of the theory, and creates it. Further parents are the third argument. The name is brief and suggestive of the theory's role. Naming and the theory listings are in [ampd012.md](ampd012.md).

`spc001.pp`–`spc005.pp` in the ProofPower source `src/hol` are reference for the language and the deductive system. None of them is kept intact. The deductive system remains that of those documents, written so that an inference rule can be executed. A rule shown to be sound can then be run. HOL4, Isabelle, and Lean may be read as exemplars. New architectural HOL is this ProofPower HOL in markdown.

The first specification is a generic theory of abstract syntax. It starts from the null-terminated byte-sequence packing in [krdd004.md](../../kr/krdd004.md#encoding-and-decoding-ntbs-and-related-data-types). The task is [amtd006.md](amtd006.md).

## Context for Writing ProofPower HOL Specifications

The foundational logical system of SPaDE is substantially similar in the substance if not in form to that of ProofPower HOL.

The relevant context falls under the following headings:

- [Points of Divergence between ProofPower HOL and SPaDE](#points-of-divergence)
- [Documentation for ProofPower HOL](#documentation-for-proofpower-hol)
- [The Theory Hierarchy](#the-theory-hierarchy)

### Points of Divergence between ProofPower HOL and SPaDE

In writing the specifications it is necessary to be aware that the system we are trying to deliver is not the same as ProofPower HOL, even though the logical system is almost identical (as an abstraction).

There are three principal points of divergence.

The first, concerns the reflexive aspects of SPaDE, which demand a new inference rule which allows functions shown to be logically sound to be applied directly in deriving further conclusions within the system.
This intended to make no difference to the theorems which are provable, but simply to shorten proofs.

To make the reasoning about the deductive system efficient, the provision for literal constants is modified to provide convenient support for term literals via an encoding of abstract syntax into byte sequences.

The third point of divergence concerns the claim to universality for declarative languge of the HOL specification language.
The alleged universality attaches not to the bare HOL logical system, but rather to something which SPaDE calls a "universal foundational institution".
This is not the place to explain that concept, but its consequence for the SPaDE logical system is a preference for strong infinity principles, effectively large cardinal axioms.
So the SPaDE variant of HOL will come with strong infinity axioms.

## Documentation for ProofPower HOL

It is likely that it will be advantageous to provide special extracts of the ProofPower documentation focussing on those aspects which are needed for the specification work required in SPaDE, but this has not yet been done and so a selection of the existing documents is cited here pro-tem.
It may be that an early task will involve creating such extracts, which can then be referenced in subsequent tasks.

There are multiple sources of documentation for ProofPower HOL, so I will provide references to the full range of available materials, together and also identify a compact subset which may be sufficient for most purposes.

The most comprehensive resource is the ProofPower repository at github.com/robarthn/pp.
The build of ProofPower creates the documentation as PDF files but for many purposes it may be more instructive to refer to source files.
SPaDEs use of ProofPower is on the utf8 branch which differs from the main branch in using utf8 character coding throughout.

The SPaDE development environment contains a clone of the utf8 branch of the ProofPower repository, which has been built and therefore contains the executables and the PDF documentation.

The documentation is also available online at:

    https://www.lemma-one.com/ProofPower/doc/doc.html

Only a few of the ProofPower manuals are relevant to SPaDE.

The relevant documents are:

- [usr001.pdf]($PPDIR/bld/doc/usr001.pdf) - ProofPower - Document preparation
This described how to prepare ProofPower source material as literate scripts in LaTeX documents.
This is not in itself directly relevant to SPaDE which does not make use of this machinery, and is not intended to accept or deliver concrete syntax.
But it may be helpful if referring to PeoofPower source documents and for constructing specifications before SPaDE reaches it target modes of operation, at which stage, though SPaDE uses "SML" embedded in markdown, the SML is a dialect augmented by ProofPower for the presentation of HOL paragraphs.
Until the specifications are transferred into a SPaDE native repository, this will remain the way in which HOL is used in practice for the development of SPaDE.

The following documents are linked to online copies at lemma-one.com in versions not quite the same as those which are build by the SPaDE development environment from the utf8 branch of the ProofPower repository.
Developers can access the latter at $PPDIR/bld/doc.

- [ProofPower - Document preparation]( $PPDIR/bld/doc/usr001.pdf) - (usr001.pdf) This manual describes how to prepare ProofPower source material as literate scripts in LaTeX documents.
This is not how its done in SPaDE, but the paragraph structures whereby HOL is embedded in LaTeX are the same as those which SPaDE uses for embedding HOL in markdown.
It might also be helpful in reading source documents from ProofPower.
- [ProofPower - Tutorial Manual](https://www.lemma-one.com/ProofPower/doc/usr004.pdf) - (usr004.pdf) A lightweight tutorial for ProofPower HOL.
- [ProofPower - Description](https://www.lemma-one.com/ProofPower/doc/usr005.pdf)- (usr005.pdf) This manual provides an account of the concrete syntax of ProofPower HOL. 
- [ProofPower - HOL Tutorial Notes]($PPDIR/bld/doc/usr013.pdf) - (usr013.pdf) A more substantial tutorial for ProofPower HOL.
- [ProofPower - HOL Reference Manual](https://www.lemma-one.com/ProofPower/doc/usr029.pdf) - (usr029.pdf) A comprehensive reference both for the theories provided with ProofPower HOL and for the functions available (and other objects) in the SML meta-language for programming proofs and extending the functionality of the tool.

SPaDE uses a minimal part of the ProofPower HOL theory hierarchy in its specifications.
This is important to minimise the complexity of reflexive features of SPaDE.

SPaDE specifications are children of `SPaDEroot` ([tlcd002.md](../tlcd002.md)), or of a theory which descends from it. `SPaDEroot` is opened on `rbjmisc`, from `retro/np`. The present context is the ancestry of `rbjmisc` together with `SPaDEroot`. Transition to minimal context is eventually intended, but is not a short term priority.  That reduction is deferred in [tlcd002.md](../tlcd002.md).

It will therefore be helpful to agents contributing to the SPaDE specifications to be aware of what is available in `rbjmisc`,  `SPaDEroot`, the ancestry of `basic_hol`.

The ancestry of basic_hol is documented in the ProofPower HOL reference manual [usr029](https://www.lemma-one.com/ProofPower/doc/usr029.pdf).
A more compact presentation of the ancestors of basic_hol may be found in HTML at :https://www.rbjones.com/rbjpub/pp/pptheories.html

It may however be instructive for agents seeking to contribute specifications to refer to the source file which create the theories. These source files are located in the `src` directory of the ProofPower repository and the directory SPaDE/repo/np.

The names of the relevant files are as follows:


| Theory name | Source files 
|--------------|-------------
| min | imp006.pp 
| log, init, misc | dtd023.pp, imp023.pp 
| pair | dtd023.pp, imp023.pp 
| list | dtd039.pp, imp039.pp 
| char | dtd040.pp, imp040.pp
| rbjmisc | t006.pp, t010.pp


The following formal specifications of ProofPower HOL and the HOL proof system are particularly relevant since some of these specifications will be rewritten for SPaDE, with the intention that there is no substantive change to the deductive system.

There is also a philosophical narrative (in SPaDE's [Synthetic Philosophy](../tlad001.md#synthetic-philosophy)) concerning the universality of a foundational institution, closely related to this logical system, the precise formal articulation of which will involve an account of the semantics.

The source files are available in the development environment at $PPDIR/src/hol/

- [spc001.pdf]($PPDIR/bld/doc/spc001.pdf) - HOL Formalised: Language and Overview
- [spc002.pdf]($PPDIR/bld/doc/spc002.pdf) - HOL Formalised: Semantics
- [spc003.pdf]($PPDIR/bld/doc/spc003.pdf) - HOL Formalised: Deductive System
- [spc004.pdf]($PPDIR/bld/doc/spc004.pdf) - HOL Formalised: Proof Development System
- [spc005.pdf]($PPDIR/bld/doc/spc005.pdf) - HOL Formalised: Formal Design of the Logical Kernel

The theories created by these files are also available in the spade.polydb ProofPower database.

## Supplementary Notes

There are some eccentricities in the character set used by ProofPower which may not be as easily identified by the documentation as is desirable.

### Variable Binding

Since it is based on a pure lambda calculus, all variable binding in ProofPower HOL is done by applying a function to a lambda abstraction, but in the concrete syntax, the lambda is replaced by the name of the relevant function.
In the most common example, universal quantification, the function is called ∀ which is followed by the variables being bound and the character `⦁` not `.`.
For instance, the expression ⌜∀x⦁ P(x)⌝ is syntactic sugar for applying the ∀ function to the lambda abstraction ⌜λx⦁ P(x)⌝.
Note that when supplying a HOL term in an SML script "term quotes" (`⌜⌝`), sometimes known as "quine corners" must be used to delimit the term, not conventional quotation marks.

### Specification Paragraphs

Another point to note is that when constants are defined in specification paragraphs, e.g. that introduced by `ⓈHOLCONST`, the vertical lines on the left should be formed using the character "│" rather than a conventional vertical bar "|".

### Other non-ascii Symbols

In a HOL specification (the version we are using) arbitrary UNICODE characters may be used (though some configuration may be required).
Commonly used non-ascii symbols include:

```
Greek Letters
	Γ Δ Θ Λ Ξ Π Σ Υ Φ Ψ Ω
	α β γ δ ε ζ η θ ι κ λ μ ν ξ π ρ σ τ υ φ χ ψ ω
Logic: 	∧ ∨ ¬ ∀ ∃ ⦁ × ≤ ≠ ≥ ∈ ∉ ⇔ ⇒
Set symbols: 𝔹 ℂ 𝔽 ℕ ℙ ℚ ℝ 𝕊 𝕌 ℤ ⊆ ∅ ⊂ ∩ ⋂ ∪ ⋃ ⊖
Arrows: → ⤖ ⤕ ⇻ ↔ ⤀ ⇸ ↣ ↦ ↠ ⤔
Formal Text Brackets: ⌜ ⌝ ⓣ ⓜ ⓩ Ⓢ ■ ┌ └ ╒ ├
Padding symbols	│ ─ ═  Index Brackets ⦏ ⦎
Bracketing symbols: ⟨ ⟩ ⟦ ⟧ ⦇ ⦈
Subscription and Superscription: ⋎ ⋏ ↗ ↘ ↕ Underlining: ⨽ ⨼
Relation, Sequence and Bag Symbols:  ⩥ ▷ ⩤ ◁ ⁀ ↾ ↿ ⊕ ⊎ ⨾ ∘
Miscellaneous: ⊢ ⦂ ≜ ⊥ ⊖
```
### Consistency Proofs

In writing HOL specifications for ProofPower constant definitions (which include all types of term), are introduced using a ⓈHOLCONST specification paragraph.
These allow a freedom of expression similar to the paragraphs in the specification language Z, which does not require specifications to be conservative.
But ProofPower HOL does require definitions to be conservative, non-conservative extensions must be introduced by explicit axioms.

In enforcing this constraint ProofPower will attemp to prove automatically that an extensions is conservative, by demonstrating that there already is a function available with the required characteristics.
Thus, if asked to intoduce a constant C such that P(C) ProofPower will attempt to prove that ⌜∃x⦁ P(x)⌝.

If it cannot do so, then the specification is made with a caveat which makes consistency provable, but will have to be discarged before the constant can be shown to have the required property.
This works fine, but makes theory listings more obscure.
SPaDEroot provides a mechanism to undertake a consistency proof which is beyond the automatic prover before the specification is introduced, yielding a conservative extension with a clearer theory listing.
It is nevertheless generally preferable to present the specification in a form which can be proven automatically, without requiring the additional consistency proof mechanism.
This is particularly important, for example, when the definition is recursive, because manual proofs of consistency are a lot harder than casting the definition in a form that can be automatically verified.
Examples of such definitions can be found in the theory LIST.

There is also a proof requirement to be discharged before introducing a new type constructor, which is done by identifying set of objects which represent the new type (and will be in bijection with the new type) and which must be shown to be non-empty since HOL types are required to be non-empty.
