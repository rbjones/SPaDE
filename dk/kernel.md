# The Logical Kernel of SPaDE

Though the departing point for the construction of [SPaDE](../docs/tlad001.md#spade) is the LCF paradigm, it does pretty much completely depart from it, and this document has not been brought in line with my present intentions, so probably best to pass over and come back later!

The decoupling of the knowledge repository from logical inference takes from the kernel a chunk of funtionality, and necessitates a different approach to assuring formal rigour in reasoning.

Two other intended features of [SPaDE](../docs/tlad001.md#spade) also contribute to this transformation, those which together are intended to make the system fully reflexive, i.e. able to reason using proven derived rules.
Those two are, the ability to directly evaluate "code", and the use of this facility to turn rules proven conservative in the metatheory to implement derived rules of inference.

In consequence

4. The Knowledge Repository is simply a heirarchy of versioned contexts.
A "context" is a signature, which is an assignent of types to
(constant) names, and a set of constraints.
Signatues are defined increentally by extensions,
which will normally be conservative.
An extension extends a set of contexts by adding
one or more names not present in the contexts being extended,
and a constraint on those names, which is a BOOLean term.
This is a generic representation for information of any kind,
and the representation of information using contexts
will also be used for metadata of various kinds.
Typically a context will have associated with it
other contexts which a variety of roles in the superstructures
making use of the logical kernel, but there are some key roles
for metadata which are essential to the operation of the logical kernel.

7. It is intended not only that the metalanguage in which
the logical kernel is formally specified be HOL (as it is in ProofPower),
but also that HOL will be the metalanguage in which proof ptogramming
is undertaken, and that the logical kernel and all
higher level proof programming will be written in HOL
(but it should be noted, that this is a comment only about the
underelying representation, not about the concrete syntax
(if any) of the language, for any programming language
can be represented in HOL.
Since there will be contexts in which the logical system is itself
represented, it will be possible to reason about algorithms which
perform logical inferences, and to demonstrate that they are
logically sound.
This makes it possible to treat verify the soundness of tactics,
and where a tactic is proven to be sound, it may then be trusted
without requiring it to undertake the detailed proof which would
otherwise be required.
Verified tactics might then deliver a proof generating function
rather than undetaking the proof, which could be subseqently evaluated
should details of the proof be required.
This significant departure from the LCF paradigm allows that invocation
of decision procedures may be legitimised by antecedent proof
of its soundness rather than by post hoc contruction of proofs
of each individual result.
