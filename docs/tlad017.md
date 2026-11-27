# Multilingual Aspects of SPaDE

## Introduction

SPaDE is *foundationally* mono-lingual.
It is build on a single logical foundations system, which in SPaDE is called a *foundational institution*, i.e. a single core logical system intended to be used primarily by conservative extension, but admitting strengthening by large cardinal (or strong infinity) axioms.

The formula enunciated by Frege, in his groundbreaking work on the foundations of mathematics, viz:

    Mathematics = Logic + Definitions

is but a whisker away from the (somewhat less catchy) SPaDE dictum that:

    Declarative knowledge =
            Foundational Institution
            + strong infinities
            + conservative extension

There is a class of such foundational institutions which can be seen to be of equivalent broad expressiveness, in a sense which we have not yet formally articulated, and we believe that the SPaDE foundational institution is a practical choice among these for its intended purposes.

Since these foundational institutions have equivalent expressiveness, it follows that they potentially provide alternative perspectives on the same body of declarative knowledge, which includes that represented in declarative languages of lesser generality or expressiveness.

Notwithstanding that monolingual foundation and rationale, it is intended that the SPaDE system will be multilingual in more ways than one, and this document is intended to expose the various ways in which diverse languages and notations may be supported and exploited in SPaDE.

On our present analysis the multilingual aspects of SPaDE fall under the following headings:

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

## Generic Facilities

The diversity of language to be supported suggests that generic facilities, for defining abstract syntax and semantics, might expedite matters.
Some efforts along these lines may be expected.

### ASN1 Support

One approach to generic facilities is the support for ASN1 begun in [ASN1 Generic Abstract Syntax](tlad017.md)

### Reflexion First Approach

A greater level of priority attaches to the possibility of generic facilities more closely connected with the "reflexion first" approach to SPaDE development, in which SPaDE seeks to realise safe Recursive Self Improvement (RSI) through metatheoretic reasoning about its own syntax and inference rules enabling the direct application of advanced reasoning capabilities once formally verified.

Applying generic facilities in implementing support for a reflexive foundational institution involves multiple "meta-" layers, and risks confusion between them, so I will talk here, by way of laying the ground, about those layers.

#### T-Expressions

The first step in this is the adoption of a uniform structure for the syntax of the foundational institution (HOL) and the SPaDE repository, which is convenient for the representation of abstract syntax but not specific to HOL or SPaDE.
That is the T-expression (T_ex).

The T-expression is designed to represent absract syntax of the kind that we find in an LCF-style interactive theorem prover.
In that context, the abstract syntax is given by a datatype having a set of syntactic categories and for each category a small number of contructors, one for each way of forming an element of that category.
The constructors have a name, perhaps cannically of the form "mk_xxxx" and a fixed set of arguments, each of a type corresponding to  the syntactic categories allowed at that point in the abstract syntax.

We may think of a T_expression as capturing the data associated with such a constructor, having a name (byte sequence) and a (possibly empty) list of T-expressions corresponding syntactic constituents (and the consructors parameters).
The T-expression is oriented towards the represetation of abstract syntax, but not to that of any particular language.
It is therefore suitable for more generic application to abstract syntax.

#### Describing Grammars

In order for there to be such generic facilities, we must have a language for describing grammars, the kind which in computing probably first appeared as Backus-Naur Form (BNF) for the description of context-free grammars.
And of course, for a generic facility in SPaDE we must have a representation of that language as T-expressions.

The first application of that language will be to itself, and the second to SPaDE's HOL and the structure of the entire SPaDE repository.
The generic facilities would then establish a relationship between grammers represented in that way, and the manner in which T-expressions are used to represent the syntax of the language thus described.

The second and more crucial test of the generic facilities will be their ability to describe the structure of SPaDE's HOL and the SPaDE repository, and the efficiency of the resulting representations.

What we need therefore is:

1. The abstract syntax of a language for describing abstract syntax, let's call is SpaGL (SPaDE Grammar Language). This should be given as a T-expression.
2. A semantics for SpaGL in the form of:
    2.1 a checker for well-formedness of abstract syntax descriptions and
    2.2 a checker for the well-formedness of T-expressions according to those descriptions.
3. The syntax of the SPaDE repository expressed in that grammar using that T-expression representation.
4. Generic facilities for editing T-expressions according to a SpaGL grammar.

There are some cycles here which need to be identified and made coherent.
e.g. we have to start with an idea of how a grammar will be represented as a T-expression, before we have nail down the grammar language.


1. A language for describing grammars, represented as T-expressions.
2. A semantics for that grammar description language
3. The syntax of the SPaDE respository expressed in that grammar using that T-expression representation.


### Facilities Supported for the Grammars

The first is the constructors, destructors and discriminators for the syntactic categories described by the grammar, and the checking of well-formedness of T-expressions according to the grammar.

There are then various other necessities for the SPaDE system which will be required in the first instance for HOL, but might then be implemented in a generic manner applicable to other grammars.
For example, the representation of the context necessary for type checking, and the more extended context necessary to capture the logical context which determines the meaning of expressions and in those contexts the checking of type-correctness and the correctness of deductive inference.




