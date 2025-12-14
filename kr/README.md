# The Knowledge Repository

This directory covers the architecture, design and implementation of the Knowledge Repository component of the [SPaDE](../docs/tlad001.md#spade) project.

The files in this directory are organized as follows:

- **[Philosophical Background](#philosophical-background)** (krph) - Foundational philosophical ideas influencing the design of the knowledge repository.
- **[Architectural Design](#architectural-design)** (krad) - High-level architecture and design of the knowledge repository.
- **[High Level Design](#high-level-design)** (krhd) - Detailed high-level design considerations for the knowledge repository.
- **[Detailed Design](#detailed-design)** (krdd) - Low-level design and implementation details.
- **[Code](#code)** (krcd)- Detailed formal specifications and code.
- **[Testing and Evaluation](#testing-and-evaluation)** (krte) - Prototyping strategies and implementations for the knowledge repository.
- **[Task Descriptions](#task-descriptions)** (krtd) - Task descriptions for implementing knowledge repository components.
- **[Build Configuration](#build-configuration)** (krci) - Makefiles and build configuration.

## Philosophical Background

This section includes documents that provide the philosophical context and rationale for the design of the Knowledge Repository.
This supplements the general philosophical materials in the [docs](../docs/README.md) directory.

At the moment we have three muddled documents in this section, which will be rationalised in due course.

- [krph001.md](krph001.md) - Knowledge Repository Philosophical Background
- [krph002.md](krph002.md) - Universality in the Representation of [Declarative Knowledge](../docs/tlad001.md#declarative-knowledge)
- [krph003.md](krph003.md) - Philosophical Background for the Knowledge Repository

## Architectural Design

This section includes documents that outline the architectural design of the Knowledge Repository.

- [krad001.md](krad001.md) - Knowledge Repository Architecture Overview

## High Level Design

This section includes documents that provide a high-level design of the Knowledge Repository.

- [krhd002.md](krhd002.md) - Prototyping strategies for knowledge repository development
- [krhd003.md](krhd003.md) - Scraping ProofPower HOL Theories into a [SPaDE](../docs/tlad001.md#spade) Repository

## Detailed Design

This section includes documents that provide a detailed design of the Knowledge Repository.

- [krdd001.md](krdd001.md) - ProofPower HOL interfaces for [SPaDE](../docs/tlad001.md#spade) theory export
- [krdd002.md](krdd002.md) - [SPaDE](../docs/tlad001.md#spade) Native repository format
- [krdd003.md](krdd003.md) - Formal specification of the repository structure in HOL4 SML.
- [krdd004.md](krdd004.md) - Detail descrription of Procedures for [SPaDE](../docs/tlad001.md#spade) Native Repository I/O

## Code

This section includes documents that provide detailed formal specifications or code for the Knowledge Repository.

- [krcd001.sml](krcd001.sml) - Signature describing the encoding/I/O/S-expression contracts for SPaDE Native Repository I/O
- [krcd006.sml](krcd006.sml) - HOL4 specification of [SPaDE](../docs/tlad001.md#spade) repository
- [krcd008.py](krcd008.py) - Abstract Base Classes for SPaDE Native Repository I/O (following krdd004.md)
- [krcd009.py](krcd009.py) - Concrete Python implementation of SPaDE Native Repository I/O (implements krcd008)
- [krcd010.sml](krcd010.sml) - SML signatures detailing the Native Repository encoding/I/O/S-expression contracts
- [krcd011.sml](krcd011.sml) - SML structures implementing the Native Repository encoding/I/O/S-expression contracts
- [krcd012.py](krcd012.py) - Python wrapper that delegates the Native Repository I/O ABCs to the SML implementation in krcd011.sml via a persistent ProofPower session

## Testing and Evaluation

This section includes documents that describe the testing and evaluation process for the Knowledge Repository.

- [krte001.md](krte001.md) - Knowledge repository prototyping test notes
- [krte002.py](krte002.py) - Integration tests for krcd009.py (SPaDE Native Repository I/O)
- [krte003.py](krte003.py) - Unit tests for krcd009.py (SPaDE Native Repository I/O)
- [krte004.sml](krte004.sml) - SML unit smoke tests for krcd011 Native Repository implementation
- [krte005.py](krte005.py) - Integration tests for krcd011 Native Repository implementation
- [krte006.sml](krte006.sml) - Extended SML tests covering krcd011 Native Repository I/O and S-expressions

## Task Descriptions

This section includes task descriptions for implementing knowledge repository components.

- [krtd001.md](krtd001.md) - Task Description for Python ABC for SPaDE Native Repository I/O
- [krtd002.md](krtd002.md) - Task Description for Code ad Test Low Level Native Repository I/O in SML.
- [krtd003.md](krtd003.md) - Task Description for SML Signatures for SPaDE Native Repository I/O

## Build Configuration

This section includes makefiles and build configuration.

- [krci001.mkf](krci001.mkf) - Knowledge Repository Makefile
