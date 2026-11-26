# Multilingual Aspects of SPaDE

## Introduction

SPaDE is *foundationally* mono-lingual.
It is build on a single logical foundations system, which is what we call a *foundational institution*, i.e. a single core logical system intended to be used primarily by conservative extension, but admitting strengthening by large cardinal axioms.

The formula enunciated by Frege in his groundbreaking work on the foundations of mathematics, viz:

    Mathematics = Logic + Definitions

is but a whisker away from the (somewhat less catchy) SPaDE dictum that:

    Declarative knowledge =
            Foundational Institution
            + strong infinities
            + conservative extension

There is a class of such foundational institutions which can be seen to be of equivalent broad expressiveness, in some sense which we have not yet formally articulated, and we believe that the SPaDE foundational institution is a practical choice among these for its intended purposes.

Since these foundational institutions have equivalent expressiveness, it follows that they potentially provide alternative perspectives on the same body of declarative knowledge, which includes that represented in declarative languages of lesser generality or expressiveness.

Notwithstanding that monolingual foundation and rationale, it is intended that the SPaDE system will be multilingual in more ways than one, and this document is intended to expose the various ways in which diverse languages and notations may be supported and exploited in SPaDE.

On our present analysis the multlinguial aspects of SPaDE fall under the followind headings:

- [Reflexion and Recursive Self Improvement](#reflexion-and-recursive-self-improvement)
- [Execution Engines](#execution-engines)
- [Diverse Data and Knowledge Representations](#diverse-data-and-knowledge-representations)
- [Generic Facilities](#generic-facilities)

This is not intended to be an exhaustive list, but rather a preliminary categorization of the main avenues through which multilingualism manifests in the SPaDE system.

Despite the extent to which SPaDE may prove to be multi-lingual, it is not intended that SPaDE itself will speak natural languages, and we do expect that as human "coding" becomes a thing of the past, programming languages as we know them, optimised for human intelligibility, will gradually be replaced by more formal and machine-oriented representations.
Nevertheless, representations there must be, and choice of representation is a critical aspect of the system's design and functionality.

## Reflexion and Recursive Self Improvement

SPaDE is a reflexion first foundational institution.
This means that the system is designed to reason about and improve its own reasoning processes, enabling recursive self-improvement and adaptation over time.
This is a strategy which extends into key application areas, notably, engineering design, in which we seek to establish formally verified design methods, which once proven can be applied to yield designs meeting requirements without the need for further proofs.

The starting point for such reflexion is the ability to *quote* HOL terms as well as *use* them, the abstract syntax of HOL thereby becoming part of the subject matter enabling the demonstration that derived inference rules are correct and can therefore be applied without reducing the inferences to primitive steps.

## Execution Engines

It is normal in informal mathematics to consider computations a part of rigorous mathematical proofs.
All formal proof systems, including SPaDE, rely upon the correct execution of the programs which implement the algorithms which check the correctness of proofs.

SPaDE allows the user to select the level of assurance required for the derivations.
The user may therefore choose a level which accepts the certain methods of evaluation as sufficiently reliable for the derivations.
The general pattern here is that a computational engine will evaluate an expression or program and sign a theorem asserting the results of that evaluation.
For this purpose therefore, we need an account in SPaDE of the abstract syntax of the language of the machine, and of the semantics of its evaluation, so that the results produced by the computational engine can be formally related to the expressions being evaluated.

## Diverse Data and Knowledge Representations

For the SPaDE foundational institution to provide a coherent distibuted repository encompassing the knowledge of the entire terran diaspora, it must be capable of comprehending and reasoning with a wide variety of data and knowledge forms, ranging from formal mathematical theories to empirical observations and domain-specific ontologies.

## Generic Facillities

The diversity of language to be supported suggests that generic facilities, for defining abstract syntax and semantics, might expedite matters.
Some efforts along these lines may be expected.

