# The Knowledge Repository

This directory contains the design and implementation of the Knowledge Repository component of the SPaDE project.

The files in this directory are organized as follows:

- **[Philosophical Background](#philosophical-background)** (krph) - Foundational philosophical ideas influencing the design of the knowledge repository.
- **[Architectural Design](#architectural-design)** (krad) - High-level architecture and design of the knowledge repository.
- **[High Level Design](#high-level-design)** (krhd) - Detailed high-level design considerations for the knowledge repository.
- **[Detailed Design](#detailed-design)** (krdd) - Low-level design and implementation details.
- **[Code](#code)** (krcd)- Detailed formal specifications and code.
- **[Testing and Evaluation](#testing-and-evaluation)** (krte) - Prototyping strategies and implementations for the knowledge repository.

## Philosophical Background

This section includes documents that provide the philosophical context and rationale for the design of the Knowledge Repository.
This supplements the general philosophical materials in the [docs](../docs/README.md) directory.

At the moment we have three muddled documents in this section, which will be rationalised in due course.

- [krph001.md](krph001.md) - Knowledge Repository Philosophical Background
- [krph002.md](krph002.md) - Universality in the Representation of Declarative Knowledge
- [krph003.md](krph003.md) - Philosophical Background for the Knowledge Repository

## Architectural Design

This section includes documents that outline the architectural design of the Knowledge Repository.

- [krad001.md](krad001.md) - Knowledge Repository Architecture Overview

## High Level Design

This section includes documents that provide a high-level design of the Knowledge Repository.

- [krhd002.md](krhd002.md) - Prototyping strategies for knowledge repository development
- [krhd003.md](krhd003.md) - Scraping ProofPower HOL Theories into a SPaDE Repository

## Detailed Design

This section includes documents that provide a detailed design of the Knowledge Repository.

- [krdd001.md](krdd001.md) - ProofPower HOL interfaces for SPaDE theory export
- [krdd002.md](krdd002.md) - SPaDE Native repository format
- [krdd003.md](krdd003.md) - Formal specification of the repository structure in HOL4 SML.
- [krdd004.md](krdd004.md) - Detail descrription of Procedures for SPaDE Native Repository I/O

## Code

This section includes documents that provide detailed formal specifications or code for the Knowledge Repository.

- [krcd001.sml](krcd001.sml) - Repo serialisation for HOL
- [krcd002.py](krcd002.py) - Python translation of kr/krdd001.md HOL datatypes

- [krcd003.py](krcd003.py) - Repository read and write
- [krcd004.json](krcd004.json) - JSON schema for the HOL datatype hterm
- [krcd005.sml](krcd005.sml) - ProofPower HOL Database Export
- [krcd006.sml](krcd006.sml) - HOL4 specification of SPaDE repository

## Task Descriptions

This section includes documents that describe specific tasks related to the Knowledge Repository.
- [krtd001.md](krtd001.md) - Task Description for Knowledge Repository Prototyping

## Testing and Evaluation

This section includes documents that describe the testing and evaluation process for the Knowledge Repository.

## TEMPORARY TRAILER

The following is the previous content of this file. It is being retained temporarily for reference while the new structure is being populated.
This material will either be moved into the new structure or into other documents in this directory or deleted.

## Overview

The Knowledge Repository is a core component of the SPaDE architecture that provides a distributed, shared repository for declarative knowledge. It breaks with the traditional LCF paradigm by decoupling knowledge storage from the deductive kernel, permitting the repository to be distributed and open ended.

## Key Features

- **Universal Representation**: Uses Cambridge HOL as a universal abstract representation for all declarative knowledge.  The knowledge repository does not contain concrete syntax and is not ties to any concrete physical representation, though there is a native SPaDE representation which is used for repositories constructed by SPaDE kr rather than other sources viewed as kr repos.
- **Distributed Architecture**: Supports widely distributed shared knowledge repositories and incorporates knowledge from diverse sources, provide with appropriate metadata for interpretation.
- **Version Control**: Maintains versioned contexts or theories in a WORM repository
 **Diverse Storage Support** as well as read/write support for native repositories, read access to diverse knowledge and data sources will be supported by special interfaces using metadata for interpretation.
- **Consistency Management**: Is designed to support the management of consistency across distributed repositories through metatheoretic methods (which depend on the dk and di subsystems).

## Architecture

The Knowledge Repository is structured around the concept of **contexts** which are similar to theories in other HOL ITP systems, but which are not repositories for theorems (which are held in caches managed by di specialists in each context).
The term theory is used to refer to a collection of context extensions (usually conservative) which yields a new context by introducing new names and constraints.

Metatheory is intended to be a significant feature of SPaDE, and metatheory will in general relate to specific theories, but the metadata will be held in its own distinct theories.
A major part of such metadata is expected to be the demonstration of derived rules of inference, use of which is expected to displace in SPaDE the role of tactics and other high level proof facilities in more tranditional LCF proof support.

## Contributing

See the main project [CONTRIBUTING.md](../CONTRIBUTING.md) for general guidelines.

Software supporting the knowledge repository is not a single monolith, because it is required to provide access from multiple programming languages and environments, to multiple forms of stored information viewed as theories in the repository.

We therefore require an abstract specification of the structure of the repository, and a variety of interfaces which mediate between stored data and software systems interpreting the stored representations as contexts in the repository, and presenting the interpretation in a form suitable for the specific programming environment.

There are therefore many opportunities for collaboration by contributing to the development of these interfaces and specifications.

Some stored forms will have been specifically designed for this repository, but others will be heritage formats that need to be interpreted, a process which involves making explicit the semantics of the data.
In these latter cases, the metadata supplying that interpretation may (and ideally should) be held in the knowledge repository as metatheory.
