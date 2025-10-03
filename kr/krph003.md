# Philosophical Background for the Knowledge Repository

An important feature of the SPaDE project, by comparison with prior support for reasoning in HOL is the aim to use HOL as an underlying abstract representation for declarative knowledge of all kinds, and to support an architecture for knowledge representation which is suitable for the entire body of declarative knowledge of the human race and its intelligent progeny.

This document is a first approach to turning that idea into a formal specification and implementation.

The story may be split into two parts.

## HOL as Universal Knowledge Representation

* The first part would then be the reasons for believing that the abstract syntax of Cambridge HOL is universal for the representation of declarative knowledge.
For which, see [Knowledge Representation Universality](KRUniversality.md).
However, the urgency of making that case is by no means compelling, since the project has independent merit.
I spend years trying to philosophise about this, latterly under the heading "Synthetic Philosophy" but this didn't work for me, and   SPaDE is my escape from Philosophy back into Engineering.
I did think some greatly stripped down philosophical underpinning would be appropriate, but as I consider the factors important to the success of SPaDE justification of the underlying logical system is probably not one of them..
So its likely to be progressed rather less enthusiastically than matters more crucial to the development.

## The Structure of the Repository

Under this heading then, everything important to the engineering of SPaDE is to be found, and it now seems likely that this will have to be spread over many documents, which I will try to introduce here.

I do not expect that in my lifetime we will have access to components of a Cosmic Repository located outside our Solar System, but it is intended that the structure delineated will be suitable for unbounded distrbution across the cosmos.

The top level abstract descriptions of the SPaDE repository must therefor address the way in which SPaDE envisages the integration of very many diverse local repositories into a single coherent cosmic repository.

I have adopted some exotic terminology to describe the various parts of the structure as follows:

There are three levels of repository in this exposition.

1. A _local repository_ is a repository which is under the control of a single agent, human or artificial, and is stored in a single location, though it may be replicated for safety or efficiency.
2. A _diasporic repository_ is a distributed repository spanning the knowledge of the entire intelligent progeny of a single origin of intelligence, such as Planet Earth, whose diasporic repository I refer to as the _terran_ diasporic repository.
3. The _pansophic repository_ is the aggregate of all the diasporic repositories, in the cosmos.

The architecture of the SPaDE knowledge repository is intended to satisfy the following requirements.

1. The _abstract_ structure of local repositories is suitable for the representation of all declarative knowledge, and is independent of any particular concrete representation, so that any repository of declarative knowledge may be viewed as a SPaDE repository (given suitable mediating software or metadata).
2. Any number of local repositories may be integrated into a single diasporic repository having a similar abstract structure.
This integration is primarily a way of partitioning the namespace of the diasporic repository into partitions which correpond to the namespaces of the local repositories.
The creation and maintenance of the diasporic repository is the management of that partitioning, which is achieved using folders or directories in appropriate ways.
3. The diaspora of the pansophic repository are not connected, representing disjoint domains of declarative knowledge from diaspora which have not yet engaged.
Once communication begins between two such diaspora, it is envisaged that the diaspora will be merged into a single diasporic repository, with appropriate partitioning of the namespace.

The pretensions of the SPaDE repository to be a cosmic resource are substantially derived from the design to maintain a coherent global context by partitioning the namespace, and the method whereby this is maintained as diasporic repositories merge.

This is primarily achieved by the addition of extra levels to the namespace, which introduced a little difficulty in defining what a name is and in the represention of names in the propositions of the repository.
These questions are addressed in the architectural design [krad001.md](krad001.md) and the associated formal specification [krhd004.sml](krhd004.sml).

### The Abstract Structure of the Cosmic Repository

* The second part addresses the structure proposed for a widely distributed shared repository of declarative knowledge thus represented.
That structure is manifest in more than one way.

  * The most important of those is perhaps an abstract account of the logical structure of the abstract cosmic repository which is the aggregate of all knowledge which is or can be logically viewed in the manner required by the project.

  * For each further development of this abstract structure, a specific context must be identified within that structure where it takes place, usually by extension of that context or by the elaboration of more results which are, in that context, demonstrably true.

Both of those should be specified in an abstract way.
It is then necessary to define various more concrete representations of parts or aspects of the repository.

An important such concrete representation will be the SPaDE native repository structure, which identifies how a subtree of the hierarchic repository may be stored in.a linear file.

There will then also be one or more representatons made available through APIs or protocols.
