# Knowledge Repository Architecture Overview

## Introduction

In this document an informal description of the abstract structure of the SPaDE Knowledge Repository is presented.
This is made more precise as a HOL4 formal specification in [krhd004.sml](krhd004.sml).

Part of the motivation for this structure is given in [Philosophical Background for the Knowledge Repository](krph003.md).

## Abstract and Concrete Structures

## Concrete Representations

SPaDE is designed to be agnostic as to concrete representations.
The intention is to embrace all sources of declarative knowledge satisfying certain minimal conditions, by allowing their various concrete representations to be viewed, and possibly manipulated, as SPaDE repositories.

The kinds of concrete representation which may be viewed as SPaDE repositories include:

- Persistent stored forms
- In-memory forms
- As accessed through APIs and protocols
- Concrete syntaxes

The SPaDE project will provide, for various reasons to be discussed, support for several examples of the first three kinds, but none of the last, since all the functionality of SPaDE is designed to be delivered through MCP servers and/or other A2A APIs and protocols, which are not tied to any particular concrete syntax.
It is expected that access to SPaDE repositories will normally be mediated by LLMs or subsequent generations of agentic AI, and that both code and formal specifications will ultimately become the province of AI, constructed to meet the requirements of users through dialogues in media suitable for the precise elicitation of requirements.

These concrete representations are not the subject of this document, which is concerned with the abstract structure of SPaDE repositories. That structure is independent of any particular concrete representation, but provides a basis for the design of such representations.

The SPaDE knowledge repository is a collection of name constraints, in which names are given meaning, first by assignment to each name of a type, and then by constraining the values which those names can take.
The constraint is expressed, by means of a term of type bool which is to be satisfied by any assignment of values to the names.
The terms are the terms of the simply typed lambda calculus, and the logic appropriate for reasoning about the knowledge represented in the repository is therefore closely related to Church's Simple Theory of Types, subject to certain refinements of which those adopted by the Cambridge HOL family of ITP systems are the major part (of which the most relevant are the small adjustmemts to accomodate type variables).

The types and terms here are essentially those of the variant of Higher Order Logic derived from Alonzo Church's *Simple Theory of Types* by Michael Gordon and others and known as *Cambridge HOL*, which is the logical basis of several Interactive Theorem Provers including ProofPower HOL4.
There are some complications arising from the more elaborate name space needed to ensure consistency in combining disparate repositories into a coherent whole.

Names are given to two kinds of entities, type constructors, and constants.
Constraints may involve either or both of types and constants and are usually closely coupled with the introduction of one or more new types or constants in a manner which does not further constrain the valuesany other names, in which case it is possible to prove that the extension is *conservative*, i.e. that any model of the prior names and constraints can be extended to a model of the new names and constraints.
If constraint is not associated with new names it is either non-conservative (and usually called an axiom) or irrelevant (semantically).

The name space within which this takes place ensures that all names are unique, and is structured hierarchically to support the logical combination of repositories from disparate origins.

The main features of the SPaDE repository which distinguishes it from prior HOL ITP systems are:

1. The limitation to the extensions to the logical system, conservative or not, i.e. definitions and axioms.
The SPaDE repository does not serve as a store of theorems unless those theorems are included in theories which are metatheoretic and explicitly state deribability., and is crucial to the ability to support a widely distributed shared repository of declarative knowledge, and to the conception of a cosmic repository of declarative knowledge is the structure of names in the SPaDE repository.
The structure of names in the SPaDE repository is the main feature which distinguishes it from prior HOL ITP systems, and is crucial to the ability to support a widely distributed shared repository of declarative knowledge, and to the conception of a cosmic repository of declarative knowledge.

The claim that all
Though this makes possible the combination of repositories, it is not normally desirable to be working in such a maximal context, and the use of focal AI methods to support reasoning will require that the context in which reasoning takes place is carefully curated to include only those names which are relevant to the subject matter at hand.

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

There may also be provision in the repository for the storage of theorems proven in each of these contexts, though in SPaDE, the close coupling between theories and theorems proven in those theories is relaxed, and theorem caching will be undertaken in more diverse ways by domain specific specialists.

Because the repository as a whole is intended to be widely distributed, we arrange for uniqueness of names across the repository by means similar to those used to ensure that URL's uniquely refer to their targets.
In SPaDE however, no presumption about the height and width of the hierarchy are made, allowing indefinite extension as the solar, system, galaxy and cosmos are explored.
This is accomplished by the additional provision that names are always *relative* and the top is open ended, enabling any two repositories from disparate origins to be logically combined into a single repository by adding an additional layer if necessary.

The localisation of names requires a hierarchical "directory" structure (though not all the structures which support this need be called directories) in which *theories* are the lowest level and serve to define the constants which characterise any particular subject matter.
This hierarchy of directories or folders ensures that all names are unique, and hence, if characterised by conservative means, can all be gathered together into a single consistent context.
It is not expected that work will be undertaken in that maximal context, but its coherence ensures that any context formed by selecting a limited number of parent theories of the hierarchy will also be coherent.

Careful selection of context is crucial for the effectiveness of focal AI.
The use of focal AI methods to support reasoning through domain specific specialists will require that the context in which reasoning takes place is curated to include only those names which are relevant to the subject matter at hand.
This is achieved by a hierarchy among theories which is distinct from the hierarchy of names induced by the folder structure and instead determined by an ancestry of theories through a parent/child relationship, each theory being formed by extension of one or more prior theories, which are be called its *parents*

Thus we see that the repository consists of a suitably indexed collection of HOL signatures and constraining formulae which give meaning to the names in the signatures. The first part of this specification is therefore concerned with the abstract syntax of HOL, and later parts with the superstructure which ensures uniqueness of names and logical contexts.

Its structure is therefore:

- names
- types
- terms
- theories
- folders
- repositories
- complexes of repositories
- cosmic repositories (universes)

In this, the repository is the largest structure managed by SPaDE native software.
A complex of repositories arises when repositories share an addressing scheme allowing cross referencing in the formation of contexts and securing the uniqueness of names across the complex.
Such a complex, is logically similar to a single repository, but physically distributed.

The concept of a universe acknowledges the likelihood that there are multiple sources of intelligence proliferating within the cosmos which are unknown to each other, or have not yet reached the point of systematically sharing knowledge.
Thus the universe is a collection of complexes of repositories, each complex being self contained and not sharing names with any other complex.
All that is needed to combine distinct complexes is agreement on a common addressing scheme, which may be achieved by the addition of a further layer to the hierarchy of folders, or the inclusion of one complex at some point in the hierarchy of another complex.
It may be noted that stability in these naming structures is important to the integrity of knowledge, since otherwise cross repository references may be broken.
The use of signed cryptographic hashes to protect the integrity of contexts and the connection between contexts and theorems proven in those contexts will provide a check against corruption of context by changes to the naming structure, forcing appropriate editing of affected parent links and the re-proving of affected theorems (though the theorems are not stored in the repository but are independently managed by domain specialist deductive AI agents).

Theorem proving will always take place in exactly one logical context, and access to the repository for that purpose will require the extraction of the content of the relevant context.

## S-expressions

Underlying the HOL structures in SPaDE native repositories there is replica of the LISP S-expression structure, which is a simple binary tree structure in which each node is either an atom or a pair of nodes.

This is mentioned here not because of its role in the representation of terms in the repository, but because it is used here for the structure of literal terms, which are explicit constants whose value is given by their structure as an S-expression.

```sml
Datatype: sexp =
      Atom string
    | Nil
    | Cons sexp sexp
End
```

## Names

Names are relative giving a place in the heirarchic structure relative to some given place.
They are therefore represented as a number indicating a height above the current folder, and a path downward from that folder.
Each stage selects a new folder, the last of which will be a theory.

Note that "string" here should be read as an arbitrary byte sequence, since names may contain characters outside the normal unicode range.
This might not properly correspond to HOL strings in HOL4, but is necessary to support the full range of possible names.

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
Meanwhile provision is made in this specification for terms to be relocated.

In the following we have the normal four kinds of term, variables, constants, applications and abstractions, with the addition of a term relocator.

```sml
val _ = Datatype
      `hterm = Tmv sname
             | Tmc rname htype
             | Tapp hterm hterm
             | Tabs sname htype hterm
             | Tloc rname hterm
             | Tlit sexp;             
```

## Sequents

```sml
val _ = Datatype
      `hsequent = Sg (hterm list) hterm`;
```

## Signature

```sml
Datatype: hsig =
      <| types: (rname # num)list;
         constants: (rname # htype)list
      |>
End
```

## Extension

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
      <| thname: sname;
         parents: rname list # shash;
         extensions: hext list;
         shash: shash
      |>
End
```

## Folders

Folders are used to structure the repository hierarchically, and contain theories or other folders.

```sml
val _ = Datatype `folder = Rdict (((num + sname) # 'b) list)`;
```

## Trees

I was looking for a much tighter charactersation of versioned trees, but this involved recursions in Datatype constructions which are not supported.
So this is a simpler tree datatype which will suffice.

```sml
val _ = Datatype
 `rtree =
   Rfolder (rtree rdict)   |
   Rleaf 'a`;
```

## The Repository

```sml
val _ = Datatype `hrepo = Hrepo (htheory rtree)`;
```
