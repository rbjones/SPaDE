# The Knowledge Repository

An important feature of the SPaDE project, by comparison with prior support for reasoning in HOL is the aim to use HOL as an underlying abstract representation for declarative knowledge of all kinds, and to support an architecture for knowledge representation which is suitable for the entire body of declarative knowledge of the human race and its intelligent progeny.

This document is a first approach to turning that idea into a formal specification and implementation.

The story may be split into two parts.

* The first part would then be the reasons for believing that the abstract syntax of Cambridge HOL is universal for the representation of declarative knowledge.
For which, see [Knowledge Representation Universality](KRUniversality.md).
(however, the urgency of making that case is by no means compelling, since the project has independent merit, so its likely to be progressed rather less enthusiastically than matters more crucial to the development).

* The second part addresses the structure proposed for a widely distributed shared repository of declarative knowledge thus represented.
That structure is manifest in more than one way.

  * The most important of those is perhaps an abstract account of the logical structure of the abstract cosmic repository which is the aggregate of all knowledge which is or can be logically viewed in the manner required by the project.

  * For each further development of this abstract structure, a specific context must be identified within that structure where it takes place, usually by extension of that context or by the elaboration of more results which are, in that context, demonstrably true.

Both of those should be specified in an abstract way.
It is then necessary to define various more concrete representations of parts or aspects of the repository.

An important such concrete representation will be the SPaDE native repository structure, which identifies how a subtree of the hierarchic repository may be stored in.a linear file.

There will then also be one or more representatons made available through APIs or protocols.
