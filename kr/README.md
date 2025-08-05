# Knowledge Repository (KR)

This directory contains the implementation and specifications for the Knowledge Repository component of the SPaDE project.

## Overview

The Knowledge Repository is a core component of the SPaDE architecture that provides a distributed, shared repository for declarative knowledge. It breaks with the traditional LCF paradigm by decoupling knowledge storage from the deductive kernel, enabling a more flexible and scalable architecture.

## Key Features

- **Universal Representation**: Uses Cambridge HOL as a universal abstract representation for all declarative knowledge
- **Distributed Architecture**: Supports widely distributed shared knowledge repositories
- **Version Control**: Maintains versioned contexts for knowledge evolution
- **Multi-language Support**: Supports diverse concrete syntaxes through abstract HOL representation
- **Consistency Management**: Ensures logical consistency across distributed repositories

## Architecture

The Knowledge Repository is structured around the concept of **contexts** - versioned signatures that contain:
- Type assignments for constant names
- Constraints (Boolean terms) on those names
- Metadata and relationships to other contexts

### Core Concepts

- **Context**: A signature with type assignments and constraints
- **Extension**: Conservative additions to existing contexts
- **Constraint**: Boolean terms that must be satisfied
- **Metadata**: Contexts that describe other contexts

## Directory Structure

```
kr/
├── README.md              # This file
├── src/                   # Source code implementation
├── specs/                 # Formal specifications
├── tests/                 # Test suite
└── docs/                  # KR-specific documentation
```

## Documentation

- [Knowledge Repository Overview](KnowledgeRepo.md) - Main specification
- [Universality Argument](KRUniversality.md) - Justification for HOL universality
- [Formal Specifications](specs/) - Mathematical specifications
- [API Documentation](docs/) - Interface documentation

## Implementation Status

**Current Status**: Conceptual design phase
- [x] High-level architecture defined
- [x] Core concepts identified
- [ ] Formal specifications complete
- [ ] Implementation started
- [ ] Test suite created

## Related Components

- **Deductive Kernel (dk/)**: The logical inference engine that operates on KR contexts
- **API Layer**: Interfaces for accessing and manipulating knowledge
- **Tools**: Parsers, generators, and utilities for working with knowledge

## Development Priorities

1. **Complete formal specifications** for context management
2. **Implement core context operations** (create, extend, query)
3. **Design distributed consistency protocols**
4. **Create concrete syntax parsers**
5. **Build test suite and validation tools**

## Contributing

See the main project [CONTRIBUTING.md](../CONTRIBUTING.md) for general guidelines.

For KR-specific development:
1. Review the formal specifications in `specs/`
2. Follow the architecture defined in `docs/`
3. Add tests for all new functionality
4. Update documentation for any API changes

## References

- [Cambridge HOL](https://www.cl.cam.ac.uk/research/hvg/HOL/) - The logical foundation
- [LCF Paradigm](https://en.wikipedia.org/wiki/LCF_(theorem_prover)) - Traditional approach we're evolving from
- [Distributed Systems](https://en.wikipedia.org/wiki/Distributed_computing) - Background on distributed architectures 