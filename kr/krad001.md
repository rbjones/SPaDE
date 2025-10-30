# Knowledge Repository Architecture Overview

## Introduction

In this document an informal description of the abstract structure of the [SPaDE](../docs/tlad001.md#spade) Knowledge Repository is presented.
This is made more precise as a HOL4 formal specification in [krcd006.sml](krcd006.sml).

Part of the motivation for this structure is given in [Philosophical Background for the Knowledge Repository](krph003.md).

The exposition is structured as follows:

- [Abstract and Concrete Structures](#abstract-and-concrete-structures)
- [S-Expressions](#s-expressions)
- [Names](#names)
- [Hashes](#hashes)
- [Types](#types)
- [Terms](#terms)
- [Sequents](#sequents)
- [Signatures](#signatures)
- [Extensions](#extensions)
- [Theories](#theories)
- [Folders](#folders)
- [Trees](#trees)
- [The Structure of Local Repositories](#the-structure-of-local-repositories)
- [Diasporic and Pansophic Repositories](#diasporic-and-pansophic-repositories)
- [Contexts and Views](#contexts-and-views)


## Abstract and Concrete Structures

### Concrete Representations

[SPaDE](../docs/tlad001.md#spade) is designed to be agnostic as to concrete representations.
The intention is to embrace all sources of [declarative knowledge](../docs/tlad001.md#declarative-knowledge) satisfying certain minimal conditions, by allowing their various concrete representations to be viewed, and possibly manipulated, as [SPaDE](../docs/tlad001.md#spade) repositories.

The kinds of concrete representation which may be viewed as [SPaDE](../docs/tlad001.md#spade) repositories include:

- Persistent stored forms
- In-memory forms
- As accessed through APIs and protocols
- Concrete syntaxes

The [SPaDE](../docs/tlad001.md#spade) project will provide, for various reasons to be discussed, support for several examples of the first three kinds, but none of the last, since all the functionality of [SPaDE](../docs/tlad001.md#spade) is designed to be delivered through MCP servers and/or other A2A APIs and protocols, which are not tied to any particular concrete syntax.
It is expected that access to [SPaDE](../docs/tlad001.md#spade) repositories will normally be mediated by LLMs or subsequent generations of agentic AI, and that both code and formal specifications will ultimately become the province of AI, constructed to meet the requirements of users through dialogues in media suitable for the precise elicitation of requirements.

These concrete representations are not the subject of this document, which is concerned with the abstract structure of [SPaDE](../docs/tlad001.md#spade) repositories. That structure is independent of any particular concrete representation, but provides a basis for the design of such representations.

### Abstract Structure

The [SPaDE](../docs/tlad001.md#spade) knowledge repository is a collection of name constraints, in which names are given meaning, first by assignment to each name of a type, and then by constraining the values which those names can take.
The constraint is expressed, by means of a term of type bool which is to be satisfied by any assignment of values to the names.
The terms are the terms of the simply typed lambda calculus, and the logic appropriate for reasoning about the knowledge represented in the repository is therefore closely related to Church's Simple Theory of Types, subject to certain refinements of which those adopted by the Cambridge HOL family of ITP systems are the major part (among which the most relevant are the small adjustments to accommodate type variables, and the admission of additional type constructors).

The types and terms here are essentially those of the variant of Higher Order Logic derived from Alonzo Church's *Simple Theory of Types* by Michael Gordon and others and known as *Cambridge HOL*, which is the logical basis of several Interactive Theorem Provers including ProofPower HOL, HOL4, HOL light and Isabelle HOL.
There are some complications in [SPaDE](../docs/tlad001.md#spade) arising from the more elaborate name space needed to ensure consistency in combining disparate widely distributed repositories into a coherent extensible whole.

Names are given to two kinds of entities, type constructors, and constants (terms).
Though type and term variables are used in the logic, they are not constrained by the repository.
Constraints may involve either or both of types and constants and are usually closely coupled with the introduction of one or more new types or constants in a manner which does not further constrain the valuesany other names, in which case it is normally possible to prove that the extension is *conservative*, i.e. that any model of the prior names and constraints can be extended to a model of the new names and constraints.
If a constraint is not associated with new names it is either non-conservative (and usually called an axiom) or irrelevant (semantically, but should be a demonstrable theorem).

The name space within which this takes place ensures that all names are unique, and is structured hierarchically to support the logical combination of repositories from disparate origins.

The main features of the [SPaDE](../docs/tlad001.md#spade) repository which distinguishes it from prior HOL ITP systems are:

1. The limitation to the extensions to the logical system, conservative or not, i.e. definitions and axioms.
The [SPaDE](../docs/tlad001.md#spade) repository does not serve as a store of theorems unless those theorems are included in theories which are metatheoretic and explicitly state deribability, and is crucial to the ability to support a widely distributed shared repository of [declarative knowledge](../docs/tlad001.md#declarative-knowledge), and to the conception of a cosmic repository of [declarative knowledge](../docs/tlad001.md#declarative-knowledge) is the structure of names in the [SPaDE](../docs/tlad001.md#spade) repository.
The structure of names in the [SPaDE](../docs/tlad001.md#spade) repository is the main feature which distinguishes it from prior HOL ITP systems, and is crucial to the ability to support a widely distributed shared repository of [declarative knowledge](../docs/tlad001.md#declarative-knowledge), and to the conception of a cosmic repository of [declarative knowledge](../docs/tlad001.md#declarative-knowledge).

Though this makes possible the combination of repositories, it is not normally desirable to be working in such a maximal context, and the use of [focal AI](../docs/tlad001.md#focal-intelligence-or-focal-ai) methods to support reasoning will require that the context in which reasoning takes place is carefully curated to include only those names which are relevant to the subject matter at hand.

Contexts are therefore a key concept in the use of the repository, and correspond to the organisation of formal theories in to hierarchies of theories, each theory being formed by extension of one or more prior theories, which may be called its *parents*.
A context then, determines a subset of the cosmic name space, and theorems proven in that context are valid in any larger context which includes it.

This is achieved by a distinct hierarchy among the theories which is determined by the ancestry of theories,
A context is sometimes best thought of as a *theory*, sometimes may be thought of as an abstract *language*.
Thus, for example, a theory of ordered pairs might be developed in a context whose signature includes a polymorphic operator for creating ordered pairs, and projections for extracting the left and right elements from such a pair, with constraints which ensure that these operators combine in the required way.

By contrast, for reasoning about the correctness of programs one might construct a context in which operators are available whose signature corresponds with the abstract syntax of the relevant programming language, and whose definitions capture the semantics of the language, thus providing for the representation in HOL of programs in that language.
In that case we may see the context as establishing a language, and also sufficient metatheory to reason about programs expressed in that language.

More generally, in using formal models of some engineering domain for the purpose of achieving reliable design and implementation of softare and hardware systems in that domain, the context in which that design activity takes place constitutes a language in which the necessary features of the designed systems and their role in the domain can be expressed.

Each such context is created, from a primitive context which corresponds to the primitive HOL logical system, by extensions, usually *conservative*.
Each such extension introduces names for new type constructors and/or constants, together with a constraint limiting the values which those names can take, and optionally but normally, a proven existential theorem showing that every model of the prior context can be extended to encompass these new types and constants in a way which satisfies the constraints.

There may also be provision in the repository for the storage of theorems proven in each of these contexts, though in [SPaDE](../docs/tlad001.md#spade), the close coupling between theories and theorems proven in those theories is relaxed, and theorem caching will be undertaken in more diverse ways by domain specific specialists.

Because the repository as a whole is intended to be widely distributed, we arrange for uniqueness of names across the repository by means similar to those used to ensure that URL's uniquely refer to their targets.
In [SPaDE](../docs/tlad001.md#spade) however, no presumption about the height and width of the hierarchy are made, allowing indefinite extension as the solar, system, galaxy and cosmos are explored.
This is accomplished by the additional provision that names are always *relative* and the top is open ended, enabling any two repositories from disparate origins to be logically combined into a single repository by adding an additional layer if necessary.

The localisation of names requires a hierarchical "directory" structure (though not all the structures which support this need be called directories) in which *theories* are the lowest level and serve to define the constants which characterise any particular subject matter.
This hierarchy of directories or folders ensures that all names are unique, and hence, if characterised by conservative means, can all be gathered together into a single consistent context.
It is not expected that work will be undertaken in that maximal context, but its coherence ensures that any context formed by selecting a limited number of parent theories of the hierarchy will also be coherent.

Careful selection of context is crucial for the effectiveness of [focal AI](../docs/tlad001.md#focal-intelligence-or-focal-ai).
The use of [focal AI](../docs/tlad001.md#focal-intelligence-or-focal-ai) methods to support reasoning through domain specific specialists will require that the context in which reasoning takes place is curated to include only those names which are relevant to the subject matter at hand.
This is achieved by a hierarchy among theories which is distinct from the hierarchy of names induced by the folder structure and instead determined by an ancestry of theories through a parent/child relationship, each theory being formed by extension of one or more prior theories, which are be called its *parents*

Thus we see that the repository consists of a suitably indexed collection of HOL signatures and constraining formulae which give meaning to the names in the signatures. The first part of this specification is therefore concerned with the abstract syntax of HOL, and later parts with the superstructure which ensures uniqueness of names and logical contexts.

Its structure is therefore:

- names
- types
- terms
- theories
- folders
- local repositories
- [diasporic](../docs/tlad001.md#diasporic) repositories
- the pansophic repository

In that structure, earlier parts are the components from which the later are formed, the latest defining very large name spaces encapsulating the abstract structures underlying the declarative knowledge of entire diaspora and ultimately the cosmos.

Reasoning and its products do not take place in these large structures, but in contexts associated with theories and determined by the ancestry of theories.
The context associated with a theory is formed by the union of the signatures and constraints of that theory and all its ancestors.

The concept of a pansophic universe acknowledges the likelihood that there are multiple sources of intelligence proliferating within the cosmos which are unknown to each other, or have not yet reached the point of systematically sharing knowledge.
Thus the universe is a collection of complexes of repositories, each complex being self contained and not sharing names with any other complex.
All that is needed to combine distinct complexes is agreement on a common addressing scheme, which may be achieved by the addition of a further layer to the hierarchy of folders, or the inclusion of one complex at some point in the hierarchy of another complex.
It may be noted that stability in these naming structures is important to the integrity of knowledge, since otherwise cross repository references may be broken.
The use of signed cryptographic hashes to protect the integrity of contexts and the connection between contexts and theorems proven in those contexts will provide a check against corruption of context by changes to the naming structure, forcing appropriate editing of affected parent links and the re-proving of affected theorems (though the theorems are not stored in the repository but are independently managed by domain specialist deductive AI agents).

Theorem proving will always take place in exactly one logical context, and access to the repository for that purpose will require the extraction of the content of the relevant context.

## S-expressions

Underlying the HOL structures in [SPaDE](../docs/tlad001.md#spade) native repositories there is replica of the LISP S-expression structure, which is a simple binary tree structure in which each node is either an atom or a pair of nodes.

This is mentioned here not because of its role in the representation of terms in the repository, but because it is used here for the structure of literal terms, which are explicit constants whose value is given by their structure as an S-expression.

```sml
Datatype: sexp =
      Atom string
    | Nil
    | Cons sexp sexp
End
```

Note that in HOL a string is an arbitrary finite sequence of bytes.

## Names

In order to enable the indefinite extension of the repository, and the logical combination of repositories from disparate origins, all names are *relative* and the top is open ended, enabling any two repositories from disparate origins to be logically combined into a single repository by adding an additional layer if necessary.

Names are relative, giving a place in the heirarchic structure relative to the locus of the name.
Naturally this does give rise to complications when reasoning with theorems proven in different contexts, for which some innovation in the structure of terms is required (see below).

They are therefore represented as a number indicating a height above the current theory, and a path downward from that folder, each step in the path being a simple name which selects a new folder, the last of which will be a theory.

```sml
val _ = Datatype `sname = Sn string`;
val _ = Datatype `rname = Rn num (sname list)`;
```

## Hashes

A signed cryptographic hash is a byte sequence, represented as a string (i.e. an arbitrary byte sequence).

```sml
val _ = Datatype `shash = Sh string`;
```

## Types

```sml
val _ = Datatype
        `htype = Tyv sname
               | Tyc rname (htype list)`;
```

## Terms

Because names are relative, comparing constants in terms is complicated by the possibility of using constants in distinct contexts, and the need to adjust to a common context.
There are several ways to approach this difficulty, and a final decision may not be made until prototyping is well progressed.

### Term Relocation

In an earlier version of this specification I attempted to deal with this by including in the term structure a way of relocating terms from the context of construction to some other context of use.
It has since been thought that interfering with the term structure for this purpose is not justified and other mechanisms may be used to achieve the same end.

### Literals

A second complication arises from the desire to facilitate and optimise metatheoretic reasoning, and resulted in a modification to the term structure to include *literal* terms, which are terms whose value is given by an S-expression.
This too is now thought to be an unnecessary complication, and may be better achieved by other means.
In ProofPower HOL literals are represented as constants for which there is no explicit definition, but whose meaning is given by special rules in the logic.
The distinction between defined constants and literals is made in the first instance in the parser and type checking, which syntactically distinguishes between the names allowed for constants and the syntactic structure of the available literals (numeric values, and quoted characters or strings).

SPaDE does not deal with concrete syntax, and so the distinction between defined constants and literals, and to accomodate naming conventions, potentially from other diasporic repositories allows arbitrary byte sequences as names.
The various altenatives roles for constants in terms can nevertheless be accomodated by the packing of data into the byte sequences used as names.
One way of achieving this is to pack into the byte seuqence two null terminated byte sequences, the first indicating the role of the constant (defined constant, numeric literal, string literal, etc.) and the second giving the data appropriate to that role.
THe details of this will be settled later and elsewhere, since it does not affect the abstract structure of the repository at the level we are now addressing it

### Term Structure

The term structure therefore remains as in Cambridge HOL (and Churc's STT, apart from the elaborations to the structure of types providing for type variables and defined type constructors) with four kinds of term: variables, constants, applications and abstractions.

```sml
val _ = Datatype
      `hterm = Tmv sname
             | Tmc rname htype
             | Tapp hterm hterm
             | Tabs sname htype hterm;             
```

## Sequents

```sml
val _ = Datatype
      `hsequent = Sg (hterm list) hterm`;
```

## Signatures

```sml
Datatype: hsig =
      <| types: (rname # num)list;
         constants: (rname # htype)list
      |>
End
```

## Extensions

```sml
Datatype: hext =
      <| signature: hsig;
         constraint: hterm
      |>
End
```

## Theory

```sml
Datatype: htheory =
      <| Thname: sname;
         Parents: rname list # shash;
         Extensions: hext list;
         Shash: shash
      |>
End
```

We note that the SPaDE repository does not store theorems proven in the theories, since these are managed separately by domain specialist deductive AI agents.
But the extensions in each theory are theorems, and there are outstanding issues about how to manage confidence in definitional extensions being conservative which have not yet been fully resolved, and may result in further elaboration to the structure of theories.

## Folders

Folders are used to structure the repository hierarchically, and contain theories or other folders (not both).

```sml
      val _ = Datatype `folder = Sdict (sname # 'b) list)`;
```

## Trees

I was looking for a much tighter charactersation of versioned trees, but this involved recursions in Datatype constructions which are not supported.
So this is a simpler tree datatype which will suffice.

```sml
val _ = Datatype
 `rtree =
   Sfolder ('a rtree) folder   |
   Rleaf 'a;
```

## The Structure of Local Repositories

A local repository is the concrete structure stored in a single SPaDE native repository file.
It has the distinctive feature that it is the level at which branches and versions are managed.
This is done through the top level folder of the local repository in which the tags associated with subfolders are labelled by ordered pairs constituting branch names and version numbers.
This however has no effect on the abstract structure of the repository, which remains as a tree of folders and theories.

```sml
val _ = Datatype `hrepo = Hrepo ((htheory folder) rtree)`;
```

## Diasporic and Pansophic Repositories

The whole point of [SPaDE](../docs/tlad001.md#spade)s more elaborate namespace is to support a single repository within which any parts can be selected to provide a context for reasoning and further extension.
The combination of all local repositories which are reachable from each other forms a [diasporic repository](../docs/tlad001.md#diasporic), which think of as constituting the entire knowledge reachable by the progeny of life on earth or some other point of origin.
Since there may be more than one such origin, we may think of the collection of all [diasporic](../docs/tlad001.md#diasporic) repositories as constituting the pansophic repository, which encompasses all knowledge in the cosmos.
The point of discussing a whole thus composed is to enaure that when previously disconnected diaspora encouter each other, we have a clear model of how their repositories may be logically combined.

The way in which this has been addressed has been through the heirarchic structure of relative names, open ended at the top, so that any two [diasporic](../docs/tlad001.md#diasporic) repositories may be combined by adding a further layer to the hierarchy if necessary to ensure uniqueness of names.
I don't think there is any urgency to formal modelling at this level.

## Contexts and Views

Each diaporic repository determines a [diasporic](../docs/tlad001.md#diasporic) context, which a syntactic and a semantic component.
The syntactic component is a signature and a set of constraints.
The semantic componenet is a collection of assignments of values to the names in the signature which satisfy the constraints, and is therefore called a model.
Each models determines the truth value of BOOLean terms constructed using only the names in the signature, and the soundness of the logic ensures that any term which can be proved true in the context is true in all models of the context.

The context in which reasoning takes place will normally be a small part of that [diasporic](../docs/tlad001.md#diasporic) context, and the [diasporic repository](../docs/tlad001.md#diasporic) has additional structure which facilitates the choice of a context appropriate for any particular application or theory development.

Two core mechanisms provide the bsis for this, with some additional elaborations related to integrity and security.

The core features are:

1. The definition of the [diasporic](../docs/tlad001.md#diasporic) context by a partially ordered tree of extensions.
2. The grouping of extensions into theories.

The context in which the extensions in a theory are to be interpreted is determined by the union of the signatures and constraints of the parent theories of that theory, together with all their ancestors.
A new appliction may therefore select just those parent theories needed to incorporate all the names on which the proposed extensions depend.
The context in which the extensions of that theory are then interpreted is the union of the contexts created by those parent theories.

Theorems proven in that context are signed by some more or less trusted authority as derivable in that context, usng a cryptographic hash of the theory which not only reliably identifies the theory, but also insures against its modification.
Because the integrity of theorems is established using  digital signatures, theorems do not need to be stored in the [SPaDE](../docs/tlad001.md#spade) repository, which is wholly devoted to securely recording logical contexts in which reasoning takes place rather than the resulting theorems.
[SPaDE](../docs/tlad001.md#spade) does not permit modification to theories, ensuring that the context in which any theorem is proven cannot be misconstrued.
It is possible to edit theories in a [SPaDE](../docs/tlad001.md#spade) repository, but this creates a new theory with a new name and a new hash, and any theorems proven in the prior theory remain valid in that theory, but not in the new theory.
