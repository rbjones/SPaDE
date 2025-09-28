# Philosophical Background for the Knowledge Repository

An important feature of the SPaDE project, by comparison with prior support for reasoning in HOL is the aim to use HOL as an underlying abstract representation for declarative knowledge of all kinds, and to support an architecture for knowledge representation which is suitable for the entire body of declarative knowledge of the human race and its intelligent progeny.

This document is a first approach to turning that idea into a formal specification and implementation.

The story may be split into two parts.

## [HOL as Universal Knowledge Representation]()

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

### The Abstract Structure of the Cosmic Repository

* The second part addresses the structure proposed for a widely distributed shared repository of declarative knowledge thus represented.
That structure is manifest in more than one way.

  * The most important of those is perhaps an abstract account of the logical structure of the abstract cosmic repository which is the aggregate of all knowledge which is or can be logically viewed in the manner required by the project.

  * For each further development of this abstract structure, a specific context must be identified within that structure where it takes place, usually by extension of that context or by the elaboration of more results which are, in that context, demonstrably true.

Both of those should be specified in an abstract way.
It is then necessary to define various more concrete representations of parts or aspects of the repository.

An important such concrete representation will be the SPaDE native repository structure, which identifies how a subtree of the hierarchic repository may be stored in.a linear file.

There will then also be one or more representatons made available through APIs or protocols.
