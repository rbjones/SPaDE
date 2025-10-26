# Project Structure

The [SPaDE](tlad001.md#spade) project is organized into a small number of subsystems, each serving a distinct purpose within the overall architecture. Understanding this structure is crucial for effective development and collaboration.

The primary purpose is the application of formal methods to the automation of design and implementation, in the first instance of software, but ultimately of any enterprise for which automated deductive reasoning may be used to ensure correctness.

It is not intended that this software will directly interface with human users.
It is intended to be delivered by one or more MCP servers to agentic AI systems whose work on behalf of users it will facilitate.

Support for intelligent reasoning will be organised in the [SPaDE](tlad001.md#spade) project into three sub-systems (each of which has a separate subdirectory of the SPaDE repository):

## **Knowledge Representation [(kr)](../kr/README.md)**

This subsystem focuses on how knowledge is represented within the system, including the data structures and algorithms used to manipulate that knowledge.

The system supports a widely distributed shared knowledge repository in a variety of ways.
It is expected that the stored form of these components of this repository will be variable, but that common structures, APIs and protocols will present these diverse storage media in a uniform manner for the purposes of automated reasoning and its applications.

The repository is *language neutral* insofar as being completely divorced from concrete syntax, and representing all knowledge using the elementary abstract syntax of the logical system of the Cambridge HOL Interactive Theorem Prover.
It is believed that knowledge expressed in any concrete syntax can be rendered faithfully and efficiently using the abstract syntax of HOL (this is commonly called *embedding*, of various *depths*).

## **Deductive Kernel [(dk)](../dk/README.md)**

The dk subsystem is responsible for the core reasoning capabilities of the system. This includes the implementation of logical inference mechanisms and other deductive reasoning techniques.

The functionality supplied here is core deductive capability encompassing the primitive rules of the HOL logic, and a variety of capabilities falling short of the methods of artificial intelligence.

Though the deductive kernel supports the primitive rules of the HOL logic, it also provides access also to efficient evaluation of executable HOL expressions, the application of proven derived rules (efficiently evaulated), and the use of external oracles.
Assurance of correctness does not depend upon forcing all derivations through the pimitive rules (as in the pure LCF paradigm) but is adaptable to meet the requirements of the application domain, and achieved by the use of digital signatures in the context of a hierarchy of trust among those signatories.
The kernel ensures that signatures on theorems are propagated through proofs ensuring that the integrity of theorems is explicit.

## **Deductive Intelligence [(di)](../di/README.md)**

The di subsystem encompasses higher-level reasoning strategies and techniques, including the use of machine learning and other AI methods to enhance the system's reasoning capabilities.

All theorem proving in the system takes place in a specific logical context, in which a collection of names complying with a signature and subject to defining constraints determine what sentences are true and which are derivable in the deductive system (these are not the same, the logic is not complete, though the shortfall is not significant for any known practical application).
These constitute perfect information spaces, and are therefore amenable to *[focal](tlad001.md#focal)* AI methods (such as those used in the Deepmind alpha-zero technologies).
To realise the benefits of these methods, we therefore anticipate that a separate AI expert will be trained for each such context, and that problem solving will exploit the heuristics specific to the context (theory) while subcontracting to the expert for constituent contexts any subproblems which are local to that context.

For non-trivial problems we envisage a marketplace in which multiple experts may be available for some domains and will bid for work.
