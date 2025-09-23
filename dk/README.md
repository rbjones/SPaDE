# Deductive Kernel (DK)

This directory contains the documentation prototyping and implementation of the Deductive Kernel component of the SPaDE project.
(initially written by Alan, an LLM on the basis of an insufficient briefing and not yet fully aligned with the project's goals).

## Overview

The Deductive Kernel is the core logical inference engine that ensures the rigour of the formal reasoning taking place in the SPaDE project and makes possible intelligence and productivity of the system in deductive engineering.

## Key Features

This is a conception of logical kernel derivative of but divergent from the LCF paradigm.
Its connection with the LCF paradigm will be evident in the similarity of much of the formal kernal specification with existing LCF implementations of proof support for HOL.
However certain features present in LCF systems but technically going beyond it are central to the design of the Deductive Kernel, and become dominant features in its exploitation.

- **Abstract Logical Engine**: Completely divorced from concrete syntax and persistent theory representation.
This implements the primitive inference rules of the logic and basic proof construction mechanisms.
- **Reflexive Capabilities**: The kernel admits the direct use of derived rules which are proven consistent with the specified derivability relation.
- **Derived Rules Instead of Tactics**: Derived rules play the role previously assumed by tactics, yielding the theorem which would normally be supplied by the tactic.
- **Efficient Execution**: Supports direct execution of verified algorithms

## Architecture

The Deductive Kernel operates in contexts from the Knowledge Repository and delivers theorems digitally signed as derivable in those contexts.
It provides certain basic facilities which can be engineered without AI or are provided by other trusted software systems.
Unlike traditional LCF systems, it does not manipulate the repository directly - theorems are not automatically added to contexts.
It is expected that context specialists in the di subsystem will maintain independent caches of theorems proven in their domain (context) of expertise.

### Core Concepts

- **Context**: The logical environment for inference (provided by KR)
- **Theorem**: A proposition proven to be derivable in a context
- **Tactic**: A verified algorithm for proof construction
- **Metatheory**: The theory of the logical system itself
- **Reflexive Reasoning**: The ability to reason about the system within itself

## Documentation

Barely started.

- [Kernel Overview](kernel.md) - Informal design sketch

## Development Status

Preliminary prototyping plan sketched.

- [Plan1](Plan1.md) - Deductive Kernel Development Plan

## Key Innovations

### 1. LCF Evolution

The kernel evolves beyond (aka breaks with!) the traditional LCF paradigm by:

- Separating logical inference from theory management
- Supplanting tactics with derived rules
- Enabling reflexive reasoning to verify derived rules and apply them directly.

### 2. Reflexive Capabilities

The kernel is designed to support:

- Self-analysis through metatheory
- Verification of its own algorithms
- Self-improvement through reflexive reasoning
- AI-assisted development of its own capabilities

## References

- [LCF Paradigm](https://en.wikipedia.org/wiki/LCF_(theorem_prover)) - Traditional approach
- [Cambridge HOL](https://www.cl.cam.ac.uk/research/hvg/HOL/) - Logical foundation
- [Reflexive Programming](https://en.wikipedia.org/wiki/Reflection_(computer_programming)) - Self-modifying systems
- [Metatheory](https://en.wikipedia.org/wiki/Metatheory) - Theory about theories
