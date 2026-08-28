# Universality in the Representation of Declarative Knowledge

_[this is a mess and will probably need to be completely replaced]

An important insight which underpins the design of the [SPaDE](tlad001.md#spade) project is the thesis that there are representations of [declarative knowledge](tlad001.md#declarative-knowledge) which are *universal* in the sense that declarative knowledge expressed in any declarative language can be faithfully represented in them.

Without further elaboration this claim is meaningless.
It is the purpose of this document to provide some of that further elaboration.
The main thrust is terminological, it is necessary to make precise what is meant by the terms used in the claim to universality.
Beyond that some informal supporting rationale is offered, but ultimately the thesis is sufficiently broad and strong that, like Church's Thesis it will not be susceptible of formal demonstration.

In making the terminology precise there are many points at which definitions are in some degree arbitrary, and there would likely be some interesting research to demonstrate that the particular choices made do not affect the plausibility of the thesis, which will probably remain beyond the scope of the SPaDE project.

## The Structure of this Exposition

In the first instance the concepts of *declarative knowledge* and the notion of "system for representing declarative knowledge" must be made precise.
The distinction between the two is essential to the thesis of universality, since it is probable that within the concept of declarative language as we will define it, there are no languages which are universal in the required sense.

The general plan is to circumscribe the class of declarative languages...

* The second is more subtle and more difficult to express.
It relates to limitation in the expressiveness of languages in which only countably many things may be said, by contrast with the richness of even the abstract universe, with its arbitrarily large cardinalities,about which we might like to talk in declarative language (let alone the concrete world, which may fall numerically short, but which is more difficult to pin semantically).
This may be read as scepticism about the expressiveness of set theory, which is in some respects the simplest of the languages which we regard as universal logical foundations for [declarative knowledge](tlad001.md#declarative-knowledge).
The strongest grounds for accepting the thesis of universality is that for more than a century there has been no advancement in the expressiveness of set theory, and no alternative contender which can claim to surpass that expressiveness.

Set theorist may regard the above as complete nonsense.
Without going into detail on exactly what I mean there by "expressiveness", its not so easy to counter such an opinion, but I will offer one little pointer to the notion of expressiveness and of logical system involved.
In the literature of the Lean system, which seems at this moment the most successful initiative and technology for the formalisation of mathematics, there is a short passage comparing the expressiveness of Lean with that of set theory, in which it is argued that they are equivalent, which to a first approximation means bi-interpretable.
To a second approximation we see that the claim is that Lean interprets one version of set theory, and a different stronger version of set theory interprets Lean.
The difference between these two versions of set theory is essentially in the "axiom of infinity", which in set theory comes as a large cardinal axiom.
To get the relevant notion of universality you need to be comparing families of logical systems indexed by the minimum cardinality of their ontologies.

First I must give an informal account of the rationale which underpins the claim to represent [declarative knowledge](tlad001.md#declarative-knowledge) in general, and in whatever declarative language it might be presented, in the abstract logical system which underpins the Cambridge HOL ITP (derivative of Church's Simple Theory of Types).

That part of the rationale concerns universal expression of abstract declarative language, i.e. language in which the syntax is abstract and the semantics is in terms of abstract entities.
A few words are needed to embrace concrete language, i.e. language about the material world.

It is implicit in the practice of formalisation using HOL that empirical phenomena can be modelled to whatever level of precision required in the purely logical system supported by the Cambridge HOL Interactive Theorem Prover (subject to limits imposed by complexity, human frailty and the state of the art)
First I must give an informal account of the rationale which underpins the claim to represent [declarative knowledge](tlad001.md#declarative-knowledge)
in general, and in whatever declarative language it might be presented, in the abstract logical system which underpins
the Cambridge HOL ITP (derivative of Church's Simple Theory of Types).

It is implicit in the practice of formalisation using HOL that empirical phenomena can be modelled to whatever level of precision required in the purely logical system supported by the Cambridge HOL Interactive Theorem Prover (subject to limits imposed by complexity, human frailty and the state of the art in and )
