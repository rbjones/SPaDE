# Declarative Knowledge in SPaDE

[Declarative knowledge](../docs/tlad001.md#declarative-knowledge) is that kind of knowledge which can be expressed in true sentences of a well defined declarative language.
A declarative language speaks of some domain of discourse using expressions whose values are determined by the state of that domain (and the values assigned to any free variables in those expressions).
A sentence in a declarative language is an expression which takes a truth value (true or false) in any given state of the domain of discourse, and has no free variables.
The semantics of the language determine the value of expressions in the language as a function of the state of the domain of discourse, and in particular, give assignmets of truth values to any free variables in the expressions.
This encompasses the truth conditions of sentences, and the sentences may therefore be used to enquire whether, or to assert or require that those conditions hold.
A body of [declarative knowledge](../docs/tlad001.md#declarative-knowledge) consists in a collection of true declarative sentences.

To say that a declarative language is *well defined* is to say the formation rules for expressions and sentences and the semantics which determine their values are precisely specified.

This account of declarative language falls well short of the kind of precision which is needed to make clear of the idea of universality, but it must serve for our present purposes.

It is now the case (as a result of historically recent advances in logic) that we have languages concerned with abstract entities whose truth conditions are very precisely known, and for which there are almost complete semi-decision procedures (algorithms which determine truth), usually presented as formal deductive systems.

The meanings of languages which concern concrete rather than abstract entities are more difficult to express precisely, but may be thought of as factored into two parts, an abstract model and a concrete interpretation.
A concrete interpretation may be given as a correspondence between some of the entities in the abstract model, and the physical objects or properties in the real world (or perhaps a fictional world) which those abstract entities are intended to represent.

If such a factorisation is used, then truth conditions for sentences about concrete entities may be expressed in terms of truth conditions for sentences about abstract entities, and will benefit from the semi-decision procedures available for the abstract interpretation of the language.
The empirical claim then follows logically from the truth of the abstract proposition and the claim that the concrete interpretation is veridical, that it correctly represents the relevant aspects of the real world.
Given formal demonstration of the abstract proposition, the empirical proposition then inherits whatever level of trust is vested in the interpretation.

This procedure can also be extended to cover language which is neither purely abstract nor simply concrete, but which addresses matters such as metaphysics or ethics.
Similar considerations apply to conclusions reached by reasoning in abstract models with interpretation in these domains of discourse.
Confidence in truth of the resulting propositions depends on that in the abstract model, and on confidence in the fidelity of the abstract model to the intended domain of discourse.

Thus abstract languages may be thought of as interpretable in many non-abstract domains, and as thereby serving to represent [declarative knowledge](../docs/tlad001.md#declarative-knowledge) about those domains.

## The Distinction between Concrete and Abstract Syntax

Language 


## Expressiveness in Declarative Languages

With this informal account of declarative knowledge, we may now consider the possibility that *the same* proposition may be expressed in many different declarative languages, and we can order the expressiveness of declarative languages according to the range of propositions which may be expressed in them.
Thus, two sentences in different declarative languages may be said to be equivalent if the abstract interpretations which are consistent with the first sentence are isomorphic to those consistent with the second sentence.  This has the consequence that any concrete interpretation of one of these sentence will have a corresponding concrete interpretation of the other sentence, and the truth of one sentence in its concrete interpretation will imply the truth of the other sentence in its corresponding concrete interpretation.
If these conditions hold then the two sentences may be said to express the same piece of declarative knowledge, and we may compare the expressiveness of declarative languages according to the range of declarative knowledge which may be expressed in them.

