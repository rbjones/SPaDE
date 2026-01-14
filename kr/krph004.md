# Declarative Knowledge in SPaDE

[Declarative knowledge](../docs/tlad001.md#declarative-knowledge) may be thought of  that kind of knowledge which can be expressed in true sentences of a well defined declarative language.
However, a simple account of declarative language, though helpful in explaining declarative knowledge will not suffice for an understanding of support for declarative knowledge in SPaDE.

## The Need for an Elaborated Conception of Declarative Language

For that some new terminology seems unavoidable, and the term *foundational institution* has been adopted.

This term will be explained in a progression, by first describing a conception of *declarative language*, then of a *foundation system*, and finally of a *foundational institution*.
The distinction may be stated concisely by observing that a declarative language *simpliciter* has a fixed syntax and vocabulary, a *foundation system* provides for arbitrary vocabulary extendable from a primitive base by means of definitions, within the context of a fixed semantics and proof system, while a *foundational institution* provides for not only the vocabulary but also the precise semantics to be extended in a well systematic manner.
Foundation systems first appeared in the work of the logicist philosophers Gottlob Frege and Bertrand Russell, initially supporting the formal development of mathematics.
The term *institution* is a more recent development in logic, associated with the work of Joseph Goguen and Rod Burstall on institutions in the 1980s, work rooted in many-sorted algebra and category theory.
The usage here in SPaDE, specifically in the term *foundational institution*, is distinct from that of Goguen and Burstall, similar only in referring to certain families of declarative languages.

Notwithstanding these two elaborations of the concept of declarative language, in any particular context in the use of a declarative foundational instution, a single definite vocabulary and semantic will be identifiable and will determine (subject to some qualitifications) the denotation of expressions and the truth conditions of sentences in that context, so we may say that each such context fixes a declarative language in the simple sense.

This elaboration of terminology serves two purposes.
The first is simply to make clear the functionality which the SPaDE system provides, and the second to underpin the claim that SPaDE provides a *universal* representation for declarative knowledge, since, though there are no universal declarative languages, there may be universal foundational institutions in which all declarative knowledge may be represented.

That was the concise account, and the remainder of this document elaborates the ideas involved.
Ultimately, the metatheoretic reflection which SPaDE seeks to exploit demands fully formal accounts of these ideas, but for present purposes further informal elaboration will have to suffice.

## An Informal Account of Declarative Language

A sentence in a declarative language is an expression which takes a truth value (true or false) in any given state of the domain of discourse, and has no free variables.
The semantics of the language determine the value of expressions in the language as a function of the state of the domain of discourse, and in particular, give assignmets of truth values to any free variables in the expressions.
This encompasses the truth conditions of sentences, and the sentences may therefore be used to enquire whether, or to assert or require that those conditions hold.
A body of [declarative knowledge](../docs/tlad001.md#declarative-knowledge) consists in a collection of true declarative sentences.

To say that a declarative language is *well defined* is to say the formation rules for expressions and sentences and the semantics which determine their values are precisely specified.

This account of declarative language falls well short of the kind of precision which is needed to make clear of the idea of universality, but it must serve for our present purposes.

## The Distinction between Concrete and Abstract Semantics

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

The distinction between concrete and abstract semantics appears at first in the early work of scientists at the Programming Research Group of Oxford University, in PRG-1, Henry F. Ledgard's "Production Systems: A Formalism for Specifying the Syntax and Translation of Computer Languages" and  later in in PRG-6, "Towards a Mathematical Semantics for Computer Languages"
by Christopher Strachey and Dana Scott, 1971.

It reflects the distinction between the kind of syntactic presentation of a language which is convenient for use by human users, and that which is convenient for formal manipulation by machines, or in metatheory such as formal semantics for programming languages.
This is particularly significant many decades later as coding, and formal work more generally is becoming the purview of machines rather than humans, and we may anticipate that concrete syntax will become less significant in the future, just as formally precise abstract representations become more widespread and significant in all fields of knowledge.
As yet, beyond GAI support for coding, there is little sign of this progression, but its progression is central to the SPaDE project.

The first thing to say about this distinction in relation to SPaDE is that SPaDE is intended to provide a service to AI systems, and not directly to human users, and is therefore not concerned with concrete syntax.
This is qualified by the necessities of that interface with Agentic AI clients, in which the use of Model Context Protocol is intended, which uses the concrete syntax of JSON.

The second is that in order to provide a repository and inference services for declarative knowledge in general, SPaDE pushes out the boat on the degree of abstraction in the syntax by adopting very simple underlying abstract structures which are suitable for representing the abstract syntax of arbitrary declarative languages.

## Expressiveness in Declarative Languages

With this informal account of declarative knowledge, we may now consider the possibility that *the same* proposition may be expressed in many different declarative languages, and we can order the expressiveness of declarative languages according to the range of propositions which may be expressed in them.
Thus, two sentences in different declarative languages may be said to be equivalent if the abstract interpretations which are consistent with the first sentence are isomorphic to those consistent with the second sentence.  This has the consequence that any concrete interpretation of one of these sentence will have a corresponding concrete interpretation of the other sentence, and the truth of one sentence in its concrete interpretation will imply the truth of the other sentence in its corresponding concrete interpretation.
If these conditions hold then the two sentences may be said to express the same piece of declarative knowledge, and we may compare the expressiveness of declarative languages according to the range of declarative knowledge which may be expressed in them.

