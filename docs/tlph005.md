# The Deductive Paradigm Shift

This document introduces the concept of a deductive paradigm shift in information processing.
It consists of two main parts, the first giving a general characterisation of the deductive paradigm and its relationship to the present computational paradigm, the second providing more specific details of how this project is intended to contribute to such a paradigm shift.

## General Characteristics

In the present computational paradigm, computer programs operate on various data, which typically have real-world signficance informally understood but not formally expressed.
If you write down what that data means, you should get a declarative sentence expressing a proposition which captures that meaning.
The computation produces new data the real-world significance of which is also only informally understood, and which could in principle be made explicit as a declarative sentence.
There is here, in the computation, a deductive connection.
We hope that the computation effects a deductive inference from the proposition which expresses significance of the input data, to that which expresses the signficance of the output data (in the context of a suitable formal model of the system in the context of which these propositions are to be understood).

If this were transformed from a computational process to a properly (rather than implicitly) deductive process, then the meanings of these data structures and the effects of computation are explicit, and the process may more formally be considered to be deductive.

Why would we want to do this, what are the potential benefits and disadvantages and costs?
How might it be accomplished, what are the difficulties downsides and costs?

Three touted benefits:

1. Formal description of the intended effects of a program makes possible the formal verification that the program achieves those effects.
This is potentially more conclusive than testing the program, since testing is always incomplete but deductive proof can show that all cases are correctly computed.

2. Formal logical systems of sufficient power to enable a transition to a deductive paradigm date back only about a century, but the complexity of derivations in such systems is prohibitive without Artificial Intelligence.

Key features of the deductive paradigm:

1. The signficance of data is made formally explicit, so that the data can be read as [declarative knowledge](tlad001.md#declarative-knowledge).

2. Information Processing is specified in terms of the inference

## Support for the Deductive Paradigm in SPaDE

### The representation of Declarative Knowledge

The central pillar of support for the deductive paradigm comes from the theoretical and practical universality of the abstract representation for [declarative knowledge](tlad001.md#declarative-knowledge) adopted by the project, Higher Order Logic.

The Universality of this representation not only permits it to integrate materials developed using more elaborate logical systems, but also to provide declarative views of diverse data sources, one metadata addressing the semantics of these sources is supplied (typically by semantic embedding.)

Similar considerations apply to the processing of such data outside of [SPaDE](tlad001.md#spade), which if furnished with suitable formal specifications can enable data processing to be understood as deductive inference.

### The Knowledge Repository

The Knowledge Repository is a virtual distributed repository which not only includes [declarative knowledge](tlad001.md#declarative-knowledge) created as such for this project or imported from other logical systems, but also views of data in any other form, imported and represented in the same abstract form suitable for deductive reasoning in the system.

The support for this knowledge repository consists of APIs which allow a variety of distinct sources to viewed as part of a distributed repository and imported in a standard form for processing in [spade](tlad001.md#spade).

### The Deductive Kernel

The deductive kernel is responsible for ensuring the integrity and soundness of the deductive inferences made within the system.
It has a structure which is derived from but diverges from strict adherence to the LCF paradigm, in which deductive reasoning is systematically reduced to a small set of primitive inference rules.

When similar tasks are accomplished by proofs in an LCF system to those which would under the computational paradigm have been directly computed, very considerable additional costs are incurred.

The divergence from the strict letter of the LCF paradigm in [SPaDE](tlad001.md#spade) comes in three principal ways, of which the first two are not original in [SPaDE](tlad001.md#spade):

1. Admitting direct computation into proofs

2. Allowing proven derived rules to be applied directly in a proof.

3. Replacing the tactical machinery which enhances kernel capabilities in an LCF system with the systematic use of proven derived rules.

### Deductive Intelligence

Deductive Intelligence in [SPaDE](tlad001.md#spade) comes through the use of artificial intelligence outside the deductive kernel to optimise all use of [deduction](tlad001.md#deduction) in the system.
Because of the complexity of detailed formal proofs, even when enhanced by oracles and reflection in the kernel, progression to widespread adoption of a deductive paradigm depends on the effective integration of AI techniques to assist in proof construction and verification.

The approach which will be taken to this falls under the general heading of [focal engineering](tlph004.md).
This approach is intended because [deduction](tlad001.md#deduction) in formally defined theories constitutes a *perfect information space* similar to those for which the DeepMind alpha-zero system was developed, and it therefore to be addressed by similar methods in [SPaDE](tlad001.md#spade), which make use of neural nets trained narrowly for these specific domains, rather than being trained using a very broad range of materials.

A significant difference is that deductive intelligence is targetted at not one such perfect information space, but a complex heirarchy corresponding to the theory structure in the distributed knowledge repository.
It is therefore intended that specialists will be trained for each theory as the theory develops, and that these will in some cases constitute a layered neural net, and in others by a heirarchy of intelligent agents each with its own area of expertise.

Deductive Intelligence contributes to the deductive paradigm primarily by overcoming the infeasibility of proof search in the absence of effective heuristics.

Further details on how it is intended to approach this problem will in due course be found in the [di](../di/README.md) directory.
