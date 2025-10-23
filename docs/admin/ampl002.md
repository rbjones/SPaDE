# SPaDE Prototyping Strategy

The prototyping strategy for [SPaDE](../tlad001.md#spade) is organised to enable the earliest possible prototyping of the most important and difficult aspects of the proposed architecture.

This means that certain capabilities essential for testing key features will be introduced at first in a very simplified form to enable prototyping of other features.

This document therefore begin's with a tentative list of those key features that we need prototyping to explore and evaluate, and then an account of how those can be simplified when necessary to support prototyping of other key features, incorporated into a partial timeline.

## Key Features to be Prototyped

1. **Delivery by MCP server**, allowing for charging or free access to services.
2. **[SPaDE](../tlad001.md#spade) Native Repositories**, populated from established theory hierarchies, read only access in first instance.
3. **Proof by Primitive Rules** of HOL logic, first prototyping can cover many aspects of the system with only propositional reasoning.
4. **Context Sensitive Alpha-Zero Proof Capability** This can be prototyped in the first instance while only primitive rules are available.
5. **Efficient Execution** This is desirable in itself but is a precondition of delivering reflection (since otherwise proven derived rules will not be efficient).
6. **Metatheory and Reflection** This is fundamental to the antificipated proof paradigm in which the use of tactics is diplaced by the application of derived rules of inference, however, this is probably hard to do.

## Prototyping Phases

In order to admit advances in prototyping and evaluating all the critical features, a radically simplfied version of the whole will first be required, after which there will be some scope for independently progressing the prototyping of each subsystem in the context thus established.

The temporal structure can therefore be partially defined by first describing that initial "whole system" prototype, and then describing how the prototyping of the key features of each subsystem can be progressed.

### A First Prototype

The aim for the first prototype is to implement the core features of the native repository, viz. uploading a repository scraped from another HOL system and reading it back into memory to support a subset of the functionality expected of the subsystem (i.e. read only access).
This read facility will then be made available through an MCP server and queried through agentic LLMs.

### Repository Protyping Progression

The first MCP server depends upon:

1. Transfer of Theory Structure from ProofPower HOL to native [SPaDE](../tlad001.md#spade) repo.

2. Read access to native repo.
  This provides a basis to begin prototyping the other subsystems.
  Normally read access is expected to establish the logical context for ongoing work.
  Then:

3. Write access to a [SPaDE](../tlad001.md#spade) native repository (additions and amendments).  By appending a new version to the repository.

4. Add integrity features using digital signatures to ensure against corruption of the repository, and guarantee the logical context in which any theorem is proven.

5. Multi-repo contexts.  The ability to work with multiple repositories simultaneously, as a result of creating a theory with parents in a different repository.

6. Support for read-only meta-theoretic view of theories, in which, for example, a theory in which a constant *c* is defined has a meta-theory in which *c__def* is the defining term for the constant c.

7. Read access to non-native sources of knowledge.  Candidates for access include:
   - Access to ProofPower HOL theories without scraping them into a native [SPaDE](../tlad001.md#spade) repository.
   - Access to other HOL systems, e.g. HOL4, HOL Light, Isabelle/HOL.
   - Access to other logical systems, e.g. Coq, Lean.
   - Generic read access to general data storage types, e.g. sql databases facilitated by metadata which may either provide access as data or under some additional semantic interpretation.

### Deductive Kernel Prototyping Progression

The initial prototype does not support reasoning, thereafter the sequences runs:

1. Implementation of primitive inference rules.
2. Fast term evaluation/execution.
3. Mechanisms supporting trusted oracles.
4. Access to specific oracles, e.g. S3
5. Machinery for propagating trust status of theorems.

### Deductive Intelligence Prototyping Progression

The initial prototype does not support higher-order reasoning, thereafter the sequences runs:

1. Prototype alpha-zero propositional reasoning.
2. Extend to hierarchic theory-specific heuristics, with up-the-stack subcontracting.

## Conclusion

As yet many of these ideas remain embryonic, and it is of course the purpose of the prototyping exercises to refine and fill out the ideas.

Meanwhile each stage of prototyping will be described in greater detail to maximise the extent to which agentic AI can contribute.
Links will be placed in this document to facilitate easy navigation and reference under the appropriate heading.

Further details on prototyping may be found in the following subsystem specific documents:

- [Knowledge repository prototyping overview](../../kr/krhd002.md)
