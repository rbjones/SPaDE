# Knowledge Repository Philosophical Background

The structure of the [SPaDE](../docs/tlad001.md#spade) knowledge repository is informed by supposed philosophical insights into the nature of [declarative knowledge](../docs/tlad001.md#declarative-knowledge) and its representation.
This document is a brief account of those ideas, and the way in which they have influenced the design of the repository.
It is not intended to be a rigorous philosophical treatise, but rather an informal bald account of the ideas which have influenced the design.

## Declarative Knowledge

[Declarative knowledge](../docs/tlad001.md#declarative-knowledge) is that kind of knowledge which can be expressed in true sentences of a well defined declarative language.
A declarative language speaks of some domain of discourse using expressions whose values are determined by the state of that domain.
A sentence in a declarative language is an expression whose value is either "true" or "false".
The semantics of the language determine under what conditions a sentence is true, and the sentence may therefore be used to enquire, assert or require that those conditions hold.
A body of [declarative knowledge](../docs/tlad001.md#declarative-knowledge) consists in a collection of true declarative sentences.

To say that a declarative language is *well defined* is to say that the truth conditions of its sentences are well defined.

It is now the case (as a result of historically recent advances in logic) that we have languages concerned with abstract entities whose truth conditions are very precisely known, and for which there are almost complete semi-decision procedures (algorithms which determine truth), usually presented as formal deductive systems.

The meanings of languages which are about concrete rather than abstract entities are more difficult to express precisely, but may be though of a factored into two parts, an abstract model and a concrete interpretation.
A concrete interpretation is a correspondence between some of the entities in the abstract model, and physical objects or properties in the real world (or perhaps a fictional world).

If such a factoring is used, then truth conditions for sentences about concrete entities may be expressed in terms of truth conditions for sentences about abstract entities, and will benefit from the semi-decision procedures available for the abstract part of the language.
The empirical claim then follows logically from the truth of the abstract proposition and the claim that the concrete interpretation is veridical.
Given formal demonstration of the abstract proposition, the empirical proposition then inherits whatever level of trust is vested in the interpretation.

This procedure can also be extended to cover language which is neither purely abstract nor simply concrete, but which addresses matters such as metaphysics or ethics.
Similar considerations apply to conclusions reached by reasoning in abstract models with interpretation in these domains of discourse.
Confidence in truth of the resulting propositions depends on that in the abstract model, and on confidence in the fidelity of the abstract model to the intended domain of discourse.

Thus abstract languages may be thought of as interpretable in many non-abstract domains, and as thereby serving to represent [declarative knowledge](../docs/tlad001.md#declarative-knowledge) about those domains.

## Universality

Among abstract languages there are differences of expressiveness, and a suitably defined notion of reducibility may be used to compare their expressive power.
It is generally accepted that there is no abstract language which is maximally expressive.
However, the syntax of many languages is capable of interpretation according to a hierarchy of abstract ontologies which may be thought to span the entire range of abstract semantic expressiveness.
The best known of these is first order set theory, whose models are the initial segments of the cumulative hierarchy of sets.
Though none of those models gives first order set theory a universal semantics, it is thought that any abstract declarative language is reducible to any member of a suitably late starting trailing segment of that family of set theories.
In terms of the relevant near complete semi-decision procedures, large cardinal axioms suffice for a while, but eventually human intuition about these principles runs must out.

In practice, and in particular, for the purposes of the kinds of reasoning required for reliable and effective engineering design, relatively weak large cardinal axioms suffice to yield something which we may think of as practically universal.

Though it is set theory which is most likely to be understood as practically universal in this way, there are many other abstract logical systems which are equally expressive, if furnished with the similarly lavish ontologies and corresponding large cardinal axioms.
Cardinality of ontology is the crucial factor.

It is therefore alleged, that practically universal languages for the representation of [declarative knowledge](../docs/tlad001.md#declarative-knowledge) are plentiful, and we may then pass to more mudane questions affecting the choice of a single such foundation system for knowledge representation.
