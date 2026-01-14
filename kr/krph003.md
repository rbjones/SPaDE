# The Structure of the SPaDE Repository

Under this heading then, everything important to the engineering of [SPaDE](../docs/tlad001.md#spade) is to be found, and it now seems likely that this will have to be spread over many documents, which I will try to introduce here.

I do not expect that in my lifetime we will have access to components of a Cosmic Repository located outside our Solar System, but it is intended that the structure delineated will be suitable for unbounded distrbution across the cosmos.

The top level abstract descriptions of the [SPaDE](../docs/tlad001.md#spade) repository must therefor address the way in which [SPaDE](../docs/tlad001.md#spade) envisages the integration of very many diverse local repositories into a single coherent cosmic repository.

I have adopted some exotic terminology to describe the various parts of the structure as follows:

There are three levels of repository in this exposition.

1. A _local repository_ is a repository which is under the control of a single agent, human or artificial, and is stored in a single location, though it may be replicated for safety or efficiency.
2. A _[diasporic repository](../docs/tlad001.md#diasporic)_ is a distributed repository spanning the knowledge of the entire intelligent progeny of a single origin of intelligence, such as Planet Earth, whose [diasporic repository](../docs/tlad001.md#diasporic) I refer to as the _[terran](../docs/tlad001.md#terran)_ [diasporic repository](../docs/tlad001.md#diasporic).
3. The _pansophic repository_ is the aggregate of all the [diasporic](../docs/tlad001.md#diasporic) repositories, in the cosmos.

The architecture of the [SPaDE](../docs/tlad001.md#spade) knowledge repository is intended to satisfy the following requirements.

1. The _abstract_ structure of local repositories is suitable for the representation of all [declarative knowledge](../docs/tlad001.md#declarative-knowledge), and is independent of any particular concrete representation, so that any repository of [declarative knowledge](../docs/tlad001.md#declarative-knowledge) may be viewed as a [SPaDE](../docs/tlad001.md#spade) repository (given suitable mediating software or metadata).
2. Any number of local repositories may be integrated into a single [diasporic repository](../docs/tlad001.md#diasporic) having a similar abstract structure.
This integration is primarily a way of partitioning the namespace of the [diasporic repository](../docs/tlad001.md#diasporic) into partitions which correpond to the namespaces of the local repositories.
The creation and maintenance of the [diasporic repository](../docs/tlad001.md#diasporic) is the management of that partitioning, which is achieved using folders or directories in appropriate ways.
3. The diaspora of the pansophic repository are not connected, representing disjoint domains of declarative knowledge from diaspora which have not yet engaged.
Once communication begins between two such diaspora, it is envisaged that the diaspora will be merged into a single [diasporic repository](../docs/tlad001.md#diasporic), with appropriate partitioning of the namespace.

The pretensions of the [SPaDE](../docs/tlad001.md#spade) repository to be a cosmic resource are substantially derived from the design to maintain a coherent global context by partitioning the namespace, and the method whereby this is maintained as [diasporic](../docs/tlad001.md#diasporic) repositories merge.

This is primarily achieved by the addition of extra levels to the namespace, which introduced a little difficulty in defining what a name is and in the represention of names in the propositions of the repository.
These questions are addressed in the architectural design [krad001.md](krad001.md) and the associated formal specification [krcd006.sml](krcd006.sml).

### The Abstract Structure of the Pansophic Repository

* The second part addresses the structure proposed for a widely distributed shared repository of [declarative knowledge](../docs/tlad001.md#declarative-knowledge) thus represented.
That structure is manifest in more than one way.

  * The most important of those is perhaps an abstract account of the logical structure of the abstract pansophic repository which is the aggregate of all knowledge which is or can be logically viewed in the manner required by the project.

  * For each further development of this abstract structure, a specific context must be identified within that structure where it takes place, usually by extension of that context or by the elaboration of more results which are, in that context, demonstrably true.

Both of those should be specified in an abstract way.
It is then necessary to define various more concrete representations of parts or aspects of the repository.

An important such concrete representation will be the [SPaDE](../docs/tlad001.md#spade) native repository structure, which identifies how a subtree of the hierarchic repository may be stored in.a linear file.

There will then also be one or more representatons made available through APIs or protocols.
