# Knowledge Repository Data Structures and Interfaces

Because the SPaDE knowledge repository is central to every aspect of the project, its data structures and interfaces are relevant to all SPaDE subsystems and are therefore enumerated here, with links to fuller documentation.

Some of the more abstract perspectives on the SPaDE knowledge repository do properly belong in the top level architecture.

## Abstract Models of the Knowledge Repository

A SPaDE repository represents declarative knowledge by introducing names for elements of a [foundational ontology](./tlad001.md#foundational-ontology) and thereby creating a language in which claims about structures of interest can be expressed.
The language thereby created speaks of abstract models, and truths about those models are logical consequences of the defining constraints on those names and can be established with confidence by deduction within the SPaDE foundational logic from those constraints.

There is some terminological awkwardness when speaking in the same context of the semantics of declarative knowledge and its manner of application to the material world.
On the one hand, it is common in metatheory when defining or discussing semantics to use the term "model" to speak of a structure which satisfies the constraints imposed by a theory.
On the other hand, in less formal discussion of the ways in which formal language can support reasoning about the material world (or any other domain) to talk of abstract theories as providing models of the matters of interest.
Both of these uses are important to SPaDE, and neither is easily replaced by different terminology, so we will use the term "model" in both senses, relying on context to disambiguate.

The following kinds of abstract structure are defined:

- simple name
- relative name
- constraint
- extension
- theory
- context
- view
- cache
