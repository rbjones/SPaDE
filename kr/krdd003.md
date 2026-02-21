# Detailed Design for ProofPower HOL Database Export

This page concerns the export of theories from the ProofPower HOL theorem prover into [SPaDE](../docs/tlad001.md#spade) knowledge repositories.
It is a detailed informal description of the algorithm to be implemented in the export tool.

 Other relevant documents are:

- [The ProofPower HOL interface for SPaDE](krdd001.md), in which the functions available in ProofPower for accessing the content of the theory hierarchy are described.
- [The SPaDE Native Repository](krdd002.md), which outlines the structure and organization of [SPaDE](../docs/tlad001.md#spade) knowledge repositories.

The export facility is to use to ProofPower HOL interface to extract the content of theories in a ProofPower HOL installation, and to create a [SPaDE](../docs/tlad001.md#spade) native repository containing that content.

## Overview of the Export Process

### Alternatives to Export

Export is only one way of accessing in [SPaDE](../docs/tlad001.md#spade) knowledge or data which is not native to [SPaDE](../docs/tlad001.md#spade).

It is also possible in principle to provide software which provides a [SPaDE](../docs/tlad001.md#spade) compatible view of other data sources without exporting them to a [SPaDE](../docs/tlad001.md#spade) native repository, and it is likely that this will be done for some important sources of data.
To support that kind of access you need to know the view presented to applications of [SPaDE](../docs/tlad001.md#spade) repositories, which will typically be through appropriate SDKs for the programming languages involved.

If such a repository is to be used by the deductive kernel or deductive intelligence then it will need to be accessed by the kr component of [SPaDE](../docs/tlad001.md#spade), and presented to the deductive parts together with any other sources relevant to the application.
That interface is not the subject of this document, and has not yet been defined.

### Common Code

This more general requirement has some similarities to the export process which is the subject of this document, and so it is worth noting some of the issues which will arise, and designing the export application to enable reuse of code for that purpose.

The principal feature common to both export and viewing is that the content of the repository must be extracted in a form which is compatible with the logical structure of [SPaDE](../docs/tlad001.md#spade) repositories.

The writing of the [SPaDE](../docs/tlad001.md#spade) native repository might then be common code for all export from repositories accessible in SML, and the extraction from the HOL theory structure would also be suitable for an application which provided a [SPaDE](../docs/tlad001.md#spade) view of the HOL theories without exporting them.

Key to this decomposition of the extraction is the design of an SML representation of a [SPaDE](../docs/tlad001.md#spade) repository, which is the subject of the next section.

### SML Representation of a SPaDE Repository

The design of an SML representation of a [SPaDE](../docs/tlad001.md#spade) repository provides a target for access to all non-native repositories which are accessed by SML (this includes ProofPower HOL, HOL4, and Isabelle HOL).

The abstract structure of a [SPaDE](../docs/tlad001.md#spade) repository is formally specified in HOL4 in [Knowledge Repository Architecture Overview](krad001.md).
This may be a sufficient basis for coding the required SML data structures for representing a [SPaDE](../docs/tlad001.md#spade) repository in memory, we await feedback on design review before coding.

### The Structure of a SPaDE Native Repository

Initially [SPaDE](../docs/tlad001.md#spade) will only provide full read/write support for repositories in its own native format, which is a binary file format used as a WORM repository.

### Writing the SPaDE Native Repository

The coding of a [SPaDE](../docs/tlad001.md#spade) repository into that byte sequence is described in [The SPaDE Native Repository](krdd002.md).

### The Extraction Algorithm

The extraction algorithm is responsible for retrieving the content from a non-native repository (such as ProofPower HOL) and transforming it into a format compatible with the [SPaDE](../docs/tlad001.md#spade) native repository structure. This involves several key steps:

1. **Accessing the Non-Native Repository**: Use the appropriate SML interface to connect to the non-native repository and access its content.
The interfaces in ProofPower HOL are described in [The ProofPower HOL interface for SPaDE](krdd001.md).

2. **Transforming the Content**: The process of transforming the content from the non-native format to the [SPaDE](../docs/tlad001.md#spade) format is relatively straightforward, as both HOL and [SPaDE](../docs/tlad001.md#spade) use higher-order logic, with almost the same underlying abstract syntax.
The main innovation in [SPaDE](../docs/tlad001.md#spade) is the more elaborate name structure to ensure name uniqueness in a distributed environment, and the use of relative paths for names to allow for upward and outward expansion of the name space.
The transformation will therefore mainly involve adjusting names to fit the [SPaDE](../docs/tlad001.md#spade) naming conventions and ensuring that all necessary context information is included.
