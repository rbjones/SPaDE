# Knowledge Repository (KR)

This directory contains the design and implementation of the Knowledge Repository component of the SPaDE project.

## Overview

The Knowledge Repository is a core component of the SPaDE architecture that provides a distributed, shared repository for declarative knowledge. It breaks with the traditional LCF paradigm by decoupling knowledge storage from the deductive kernel, permitting the repository to be distributed and open ended.

## Key Features

- **Universal Representation**: Uses Cambridge HOL as a universal abstract representation for all declarative knowledge.  The knowledge repository does not contain concrete syntzx and is not ties to any concrete physical representation, though there is a native SPaDE representation which is used for repositories constructed by SPaDE kr rather than other sources viewed as kr repos.
- **Distributed Architecture**: Supports widely distributed shared knowledge repositories and incorporates knowledge from diverse sources, provide with appropriate metadata for interpretation.
- **Version Control**: Maintains versioned contexts or theories in a WORM repository
- **Multi-language Support**: Supports diverse languages through the abstract syntax of HOL (concrete syntax dealt with at other levels)
- **Diverse Storage Support** as well as read/write support for native repositories, read access to diverse knowledge and data sources will be supported by special interfaces using metadata for interpretation.
- **Consistency Management**: Ensures logical consistency across distributed repositories when contexts are extended conservatively.

## Architecture

The Knowledge Repository is structured around the concept of **contexts** - versioned signatures that contain:

- Type assignments for constant names
- Constraints (Boolean terms) on those names

A context is essentially the content of a theory and its ancestry, and because of the distributed nature of this repository, that ancestry may be drawn from disparate sources.

- Metatheory is intended to be a significant feature of SPaDE, and metatheory will in general relate to specific theories, but the metadata will be held in its own distinct theories.
A major part of such metadata is expected to be the demonstration of derived rules of inference, use of which is expected to displace in SPaDE the role of tactics and other high level proof facilities in more tranditional LCF proof support.

### Core Concepts

- **Context**: A signature with type assignments and constraints
- **Extension**: Additions to existing contexts (usually conservative)
- **Constraint**: Boolean terms giving mening to new names
- **Metadata**: Contexts about other contexts

## Documentation

- [Knowledge Repository Overview](KnowledgeRepo.md) - Main specification
- [Universality Argument](KRUniversality.md) - Justification for HOL universality

### HOL Specifications

- [h4001.md](h4001.md) HOL Abstract Syntax - Formal specification of the repository structure in HOL

### SML Code

- [m4001.sml](m4001.sml) HOL Abstract Syntax - SML translation of the repository structure in h4001.md
- [m4002.md](m4002.md) - ProofPower HOL Database Exporter Interface

### Python Code

- [p4001.py](p4001.py) - Python HOL abstract syntax
- [p4002.py](p4002.py) - Python interface to the Knowledge Repository

### Strategies Tactics and Plans

- [KRproto.md](KRproto.md) - Prototyping strategies for knowledge repository development

## Contributing

See the main project [CONTRIBUTING.md](../CONTRIBUTING.md) for general guidelines.

Software supporting the knowledge repository is not a single monolith, because it is required to provide access from multiple programming languages and environments, to multiple forms of stored information viewed as theories in the repository.

We therefore require an abstract specification of the structure of the repository, and a variety of interfaces which mediate between stored data and software systems interpreting the stored representations as contexts in the repository, and presenting that interpretation in a form suitable for the specific programming environment.

There are therefore many opportunities for collaboration by contributing to the development of these interfaces and specifications.

Some stored forms will have been specifically designed for this repository, but others will be heritage formats that need to be interpreted, a process which essentially consists in making explicit the semantics of the data.
In these latter cases, the metadata supplying that interpretation may (and ideally should) be held in the knowledge repository as metatheory.

## References

- [Cambridge HOL](https://www.cl.cam.ac.uk/research/hvg/HOL/) - The logical foundation (give or take)
- [LCF Paradigm](https://en.wikipedia.org/wiki/LCF_(theorem_prover)) - Traditional approach we're evolving from
