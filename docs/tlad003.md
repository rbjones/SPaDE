# SPaDE Project Structure

The [SPaDE](tlad001.md#spade) project is organized into a small number of subsystems, each serving a distinct purpose within the overall architecture. Understanding this structure is crucial for effective development and collaboration.

The primary purpose is the application of formal methods to the automation of design and implementation, in the first instance of software, but ultimately of any enterprise for which automated deductive reasoning may be used to ensure correctness.

It is not intended that this software will directly interface with human users.
It is intended to be delivered by one or more MCP servers to agentic AI systems whose work on behalf of users it will facilitate.

Support for intelligent reasoning will be organised in the [SPaDE](tlad001.md#spade) project into four sub-systems (each of which has a separate subdirectory of the SPaDE repository).

## Knowledge Representation [(kr)](../kr/README.md)

This subsystem focuses on how knowledge is represented within the system, including the data structures and algorithms used to manipulate that knowledge.

The system supports a widely distributed shared knowledge repository in a variety of ways.
It is expected that the stored form of these components of this repository will be variable, but that common structures, APIs and protocols will present these diverse storage media in a uniform manner for the purposes of automated reasoning and its applications.

The repository is *language neutral* insofar as being completely divorced from concrete syntax, and representing all knowledge using the elementary abstract syntax of the logical system of the Cambridge HOL Interactive Theorem Prover.
It is believed that knowledge expressed in any concrete syntax can be rendered faithfully and efficiently using the abstract syntax of HOL (this is commonly called *embedding*, of various *depths*).

## Deductive Kernel [(dk)](../dk/README.md)

In speaking of a *deductive kernel* for SPaDE it is important to distinguish SPaDE from a pure LCF style theorem prover.

It breaches that model in the usual ways, which include mechanisms for efficient evaluation of executable expressions, the admission of "oracles", and support for efficient proof algorithms validated by reflexive reasoning.

These extensions are admitted in SPaDE through the adoption of a quite different approach to integrity and trust, in which all theorems are digitally signed as true in a specific context by some authority in whom more or less trust may be placed.

The aggregation of risk as theorems are progressively derived with the help of a variety of such authorities gives rise to a theory structure in which theorems are tagged by expressions forming a lattice of trust, and each viewer of the repository selects the level of trust they require for the theorems they use and is presented with an appropriately filtered view of the repository.
The assurance metrics associated with each theorem are boolean expressions over the atomic trust levels represented by the keys used in signing theorems.

A complementary filtering is also envisaged to provide security, so that the view of any user of the repository is filtered to exclude theorems which they are not authorised to see, and also those in whose authority they do not place sufficient trust.

The deductive kernel provides a number of proof capabilities associated with distinct authorities, but is not the sole source of proof capabilities in the system.
Any person or system may sign theorems independently of the deductive kernel and sign them with any digital signature for which they have a private key.
These may then used in continuing inference or be stored in a SPaDE repository, associated with the logical context in which they are alleged to be true as endorsed by the signatory.

The deductive kernel will be capable of deriving theorems using the primitive rules of the HOL logic, and signing theorems so derived with its own key.
But it will also provide a variety of other ways in which theorems may be established, using a variety of proof techniques, each associated with distinct authorities.

## Deductive Intelligence [(di)](../di/README.md)

The di subsystem encompasses higher-level reasoning strategies and techniques, including the use of machine learning and other AI methods to enhance the system's reasoning capabilities.

All theorem proving in the system takes place in a specific logical context, in which a collection of names complying with a signature and subject to defining constraints determine what sentences are true and which are derivable in the deductive system (these are not the same, the logic is not complete, though the shortfall is not significant for any known practical application).
These constitute perfect information spaces, and are therefore amenable to *[focal](tlad001.md#focal)* AI methods (such as those used in the Deepmind alpha-zero technologies).
To realise the benefits of these methods, we therefore anticipate that a separate AI expert will be trained for each such context, and that problem solving will exploit the heuristics specific to the context (theory) while subcontracting to the expert for constituent contexts any subproblems which are local to that context.

For non-trivial problems we envisage a marketplace in which multiple experts may be available for some domains and will bid for work.

## MCP Server [(mcp)](../mcp/README.md)

The MCP server subsystem provides the interface between SPaDE and client AGI systems.
It purpose is to provide transparent and convenient access both to the distributed repository of declarative knowledge and to the reasoning capabilities of the deductive kernel and deductive intelligence subsystems.
The interface will be constructively oriented, enabling its agentic AGI clients to elicit requirements from their own clients and construct solutions using the knowledge and reasoning capabilities of the SPaDE system.
