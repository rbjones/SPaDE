# Universality in the Representation of Declarative Knowledge

## Preliminary Ruminations

A part of the rationale for SPaDE comes from the belief that there are representations of [declarative knowledge](../docs/tlad001.md#declarative-knowledge) which are universal, insofar as they can express any knowledge which might be expressed in any declarative language.
In order to make definitive a claim to universality that claim must first be made precise, an early step in which is to define the concept of declarative language.
Such a definition will inevitably be to some degree arbitrary, and will to that extent limit the scope of the universality claim.
An established method for giving plausibility to a universal claim despite the need for such arbitrary choices, is to chose multiple different approaches to the definition and show that they all define the same class of languages.
This is how Church's Thesis on the concept of "effectively computable function" was supported.

Sceptics may view the necessary arbitrary choices as a kind of gerrymandering, in the face of which I am happy to fall back on offering it as an attempt to delineate the scope of important classes of declarative language, (and thence declarative knowledge), rather than pressing for its acceptance as an absolute.
There are those who challenge Church's Thesis but is nevertheless widely accepted as delineating and important class of functions.

Having said that, I do not have here the kind of formal definition of declarative language which would be required to make the universality claim precise, which falls under a broad category of philosophical background which I would like to see made more precise, but not at the cost of delaying the development of SPaDE.

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

It is implicit in the practice of formalisation using HOL that empirical phenomena can be modelled to whatever level of precision required in the purely logical system supported by the Cambridge HOL Interactive Theorem Prover (subject to limits imposed by complexity, human frailty and the state of the art in and )
First I must give an informal account of the rationale which underpins the claim to represent [declarative knowledge](../docs/tlad001.md#declarative-knowledge)
in general, and in whatever declarative language it might be presented, in the abstract logical system which underpins
the Cambridge HOL ITP (derivative of Church's Simple Theory of Types).

## Universality (II)

An important feature of the [SPaDE](../docs/tlad001.md#spade) project, by comparison with prior support for reasoning in HOL is the aim to use HOL as an underlying abstract representation for [declarative knowledge](../docs/tlad001.md#declarative-knowledge) of all kinds, and to support an architecture for knowledge representation which is suitable for the entire body of [declarative knowledge](../docs/tlad001.md#declarative-knowledge) of the human race and its intelligent progeny.

This document is a first approach to turning that idea into a formal specification and implementation.

The story may be split into two parts.

## Universality

Among abstract languages there are differences of expressiveness, and a suitably defined notion of reducibility may be used to compare their expressive power.
It is generally accepted that there is no abstract language which is maximally expressive.
However, the syntax of many languages is capable of interpretation according to a hierarchy of abstract ontologies which may be thought to span the entire range of abstract semantic expressiveness.
The best known of these is the first order theory of well-founded sets, whose intended models are the initial segments of the cumulative hierarchy of sets.
Though none of those models gives first order set theory a universal semantics, it is thought that any abstract declarative language is reducible to any member of a suitably late starting trailing segment of that family of set theories (any sufficiently large initial segment).
In terms of the relevant near complete semi-decision procedures, large cardinal axioms suffice for a while, but eventually human intuition about these principles runs must out.

In practice, and in particular, for the purposes of the kinds of reasoning required for reliable and effective engineering design, relatively weak large cardinal axioms suffice to yield something which we may think of as practically universal.

Though it is set theory which is most likely to be understood as practically universal in this way, there are many other abstract logical systems which are equally expressive, if furnished with the similarly lavish ontologies and corresponding large cardinal axioms.
Cardinality of ontology is the crucial factor.

It is therefore alleged, that practically universal languages for the representation of [declarative knowledge](../docs/tlad001.md#declarative-knowledge) are plentiful, and we may then pass to more mundane questions affecting the choice of a single such foundation system for knowledge representation.

## HOL as Universal Knowledge Representation

* The first part would then be the reasons for believing that the abstract syntax of Cambridge HOL is universal for the representation of [declarative knowledge](../docs/tlad001.md#declarative-knowledge).
For which, see [Universality in the Representation of Declarative Knowledge](krph002.md).
However, the urgency of making that case is by no means compelling, since the project has independent merit.
I spent years trying to philosophise about this, latterly under the heading "[Synthetic Philosophy](../docs/tlad001.md#synthetic-philosophy)" but this didn't work for me, and [SPaDE](../docs/tlad001.md#spade) is my escape from Philosophy back into Engineering.
I did think some greatly stripped down philosophical underpinning would be appropriate, but as I consider the factors important to the success of [SPaDE](../docs/tlad001.md#spade) justification of the underlying logical system is probably not one of them..
So its likely to be progressed rather less enthusiastically than matters more crucial to the development.
