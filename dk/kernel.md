# kernel.md

This is an informal sketch of the new logical jernel proposed, which will proceed by enumeration of the intended departures from the ProofPower kernel as documented in the formal specifications in the series spc001-4 of the ProofPower HOL documentation.

The changes intended are quite radical so I will mention briefly
the main radical changes before moving into more detail.

1. It's probably most accurate to say that the lCF padadigm
has been abandoned.
I prefer to think of it as LCF mark 2.
The same standard of rigour is still supported, as well as
more liberal regimes.

2. The most important innovation is arguably the separation of logical
kernel from the theory management, and this comes with a substantial
reconception of the repository,
which is now presented as a potentially cosmically distributed
shared knowledge repository, suitable for the management
and exploitation of any and all declarative knowledge
(subject to a particular conception of what declarative knowledge is!)

3. Alongside that decoupling of knowledge repository and logical engine
and supporting the multilingual aspiration to embrace
all declarative knowledge, the logical engine is completely abstract
and divorced from any concrete syntax in which the material might be
presented, or stored.

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

5. The logical kernel performs logical inference in such a context,
delivering theorems derivable in the context, but does not itself
manipulate the repository.
By contrast with the typical working of the LCF paradigm,
theorems derived in a context do not become part of the context.
They may nevertheless be stored in the repository, by means of
additional contexts which add names associated with the theorems
and contraints those names to denote the theorems,
but the construction of such contexts is not undertaken by
the logical kernel.

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


6. Two major extensions to the LCF paradigm are envisaged to enable
logically sound but computationally efficient algorithms
to be directly executed and accepted as deductively sound.
The first is the evaluation of executable expressions
represented in HOL abstract syntax.
The second is the use of verified tactics, as described above, which can produce proof-generating functions or certificates that can be checked independently. These extensions aim to combine the rigour of traditional LCF-style proof with the efficiency and flexibility required for large-scale, practical formalisation.


