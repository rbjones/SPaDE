# Universality in the Representation of Declarative Knowledge

_[this is a mess and will probably need to be completely replaced]

This is an informal account of how it is that there are representations of [declarative knowledge](../docs/tlad001.md#declarative-knowledge) which are universal, insofar as they can express any knowledge which might be expressed in any declarative language.

Though this is stated in a very definite way, there are two ways in which it demands qualification.

* The first is that it depends upon a definition of _[declarative knowledge](../docs/tlad001.md#declarative-knowledge)_, which in turn rests upon a notion of _declarative language_, for both of which I would have to defer to a slightly more formal account of the thesis.

* The second is more subtle and more difficult to express, and relates to limitation in the expressiveness of language in which only countably many things may be said by contrast with the richness of just the abstract universe, with its arbitrarily large cardinalities,about which we might like to talk in declarative language.
This may be read as scepticism about the expressiveness of set theory, which is in some respects the simplest of the languages which we regard as universal logical foundations for [declarative knowledge](../docs/tlad001.md#declarative-knowledge).
The strongest grounds for accepting the thesis of universality is that for more than a century there has been no advancement in the expressiveness of set theory, and no alternative contender which can claim to surpass that expressiveness.

Set theorist may regard the above as complete nonsense.
Without going into detail on exactly what I mean there by expressiveness, its not so easy to counter such an opinion, but I will offer one little pointer to the notion of expressiveness and of logical system involved.
In the literature of the Lean system, which seems at this moment the most successful initiative and technology for the formalisation of mathematics, there is a short passage comparing the expressiveness of Lean with that of set theory, in which it is argued that they are equivalent, which to a first approximation means bi-interpretable.
To a second approximation we see that the claim is that Lean interprets one version of set theory, and a different stronger version interprets Lean.
The difference between these two versions of set theory is essentially in the "axiom of infinity", which in set theory comes as a large cardinal axiom.
So to get the relevant notion of universality you need to be comparing families of logical systems indexed by the minimum cardinality of their ontologies.

First I must give an informal account of the rationale which underpins the claim to represent [declarative knowledge](../docs/tlad001.md#declarative-knowledge) in general, and in whatever declarative language it might be presented, in the abstract logical system which underpins the Cambridge HOL ITP (derivative of Church's Simple Theory of Types).

That part of the rationale concerns universal expression of abstract declarative language, i.e. language _about_ abstract entities.
A few words are needed to embrace concrete language, i.e. language about the material world.

It is implicit in the pratice of formalisation using HOL that empirical phenomena can be modelled to whatever level of precision required in the purely logical system supported by the Cambridge HOL Interactive Theorem Prover (subject to limits imposed by complexity, human frailty and the state of the art in and )
First I must give an informal account of the rationale which underpins the claim to represent [declarative knowledge](../docs/tlad001.md#declarative-knowledge)
in general, and in whatever declarative language it might be presented, in the abstract logical system which underpins
the Cambridge HOL ITP (derivative of Church's Simple Theory of Types).
