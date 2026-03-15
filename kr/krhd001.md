# SPaDE Knowledge Repository Information Structures

- [Introduction](#introduction)
- [The Structure of the Name-Space](#the-structure-of-the-name-space)
- [Assigning Meaning to Names](#assigning-meaning-to-names)
- [Abstraction and Views]{#abstraction-and-views}

## Introduction

The purpose of this document is to describe in some detail the structure of SPaDE repositories and of the views of the repositories presented by the kr subsystem  to other subsystems of SPaDE and to the clients of the SPaDE MCP server.

## The Structure of the Name-Space

At the coarsest, there are three levels of repository, these are called "pansophic", "diasporic", and "local".

- [The Pansophic Repository](#the-pansophic-repository)
- [Diasporic Repositories](#disporic-repositories)
- [Local Repositories](#local-repositories)

### The Pansophic Repository

The pansophic level encompasses the whole universe, and consists of a set of mutually isolated diasporic repositories each of which is a maximal connected space of the pansophic knowledge repository.
The purpose of speaking of the pansophic repository is to present the allowable operations on the diasporic repositories as a consistent and organised aggregation of content within a coherent framework.

### Disporic Repositories

Each diasporic repository is a distributed hierarchy formed by the combination of local repositories, each distinguished by a unique path from the root of the diasporic repository.
The full diasporic path of a name is the concatenation of the diasporic path to a local repository with a path within that local repository.

A diasporic SPaDE repository provides a single name-space in which abstract modelling of any subject matter definite enough for declarative language expressing declarative knowledge can be made precise, enabling reliable reasoning and definite establishment of declarative truths.
These truths are applied beyond the domain of abstract structures by less formal bijections between the abstract structures and arbitrary physical or metaphysical structures of interest.
In this way SPaDE supports the representation of objective declarative language and furthers the establishment of truth wherever language can be made definite enough to be objective.

Each diasporic repository is a hierarchy in which individual names are paths from the root of the diasporic repository.
These paths are not absolute, but are relative to the root of the diasporic repository.
When diaspora make contact, the individual diaspora merge either by the incorporation of one into the other, or by the creation of a new repository above each, extending the diasporic paths with an extra element on the left.

### Local Repositories

A diasporic repository is a composed of local repositories, each distinguished by a unique path from the root of the diasporic repository.
The full diasporic path of a name is the concatenation of the diasporic path to a local repository with a path within that local repository.

The pansophic repository as a whole is therefore a set of diasporic name-spaces each of which assigns meaning to paths in a diaspora.
The pansophic repository advances by the creation of new diaspora (as new sources of intelligence evolve) augmentation of existing diaspora by the addition of new paths and constraints defining their meaning, or by the combination of two or more existing diaspora.
The augmentation of diaspora leaves unchanged the meanings assigned to existing paths in the diaspora.
All references to names are provided by relative paths from a location which is called the context of the reference.
Such references are stable under all the permitted diasporic changes.

## Assigning Meaning to Names

The constraints which give meaning to names in the repository mention other names already present in the diasporic repository, and the transitive closure of the resulting relationship of dependence gives a partial ordering on the names in the diasporic repository.
A coarse version of this ordering comes from a parent-child relationship between theories in the repositories, which acts as a limitation on the visibility of names at any location (from any context) in the repository.

## Abstraction and Views

To realise the additive nature of declarative knowledge, the pansophic repository is organised as a large namespace in which each name is uniquely reserved to a single purpose and equivocation is avoided.
Most applications build on a small part of the pansophic repository, and the rest of the repository is irrelevant to them.
It is therefore generally desirable to work in a controlled subset of the pansophic name-space.
It is also desirable to have distinct presentations of the repository for distinct purposes.

To describe these various mechanisms we adopt particular meanings for the terms "context", "view", and "presentation".

Theories group together names are are the main unit in which scoping rules are applied.

Contexts determine the scope of names, and are controlled by the parenthood relationship between theories, and by the order of the extensions in a theory.
A context is set by each theory and is the union of the contexts determined by the parents of the theory and the context determined by the extensions in the theory itself.
Each extension in a theory determines a sub-context of that determined by the theory, omitting the names not yet introduced in the theory.

Theories not only introduce new names in the context determined by the theory, but the may also hide names, either introduced by the theory or by parent theories.

A view is a subset of a context determined by position in one or more classification hierarchies.
At present just two such hierarchies are anticipated, related to integrity and confidentiality:

- a *trust* hierarchy, in relation to which a view is restricted to knowledge which depends only on and is signed by trusted sources.
- a *clearance* hierarchy, in relation to which access to some parts of the repository is restricted to those with sufficient clearance.

Each agent accessing a repository has a trust level and a clearance level, and the view of the repository presented to that agent is restricted to the part of the context determined by the theories in which all the dependencies of the names in that part are signed by trusted sources and are not classified above the clearance level of the agent.

In the first place it is the integrity provisions which must be supported, since these *replace* the integrity delivered by the LCF paradigm, allowing a greater variety of proof methods to be used, and allowing the use of untrusted proof methods without compromising the integrity of the repository.
An agent accessing a repository stipulates a required integrity level, and will then see only those results which depend only methods which meet the required integrity level.
Each theorem is signed as derivable in some context using a key which is associated with the integrity level of the method used, and is qualified by the integrity levels of the theorems from which it was derived.
In addition to the signing of all theorems, the integrity of the context in which they are derived must be established, which is done by signing incremental cryprographic hashes.
