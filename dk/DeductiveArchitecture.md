# SPaDE Deductive Architecture

The [SPaDE](../docs/tlad001.md#spade) Deductive Architecture is derived from the LCF paradigm, but now diverges too far from it to be properly described as following the LCF paradigm.

## Core Inference Mechanisms

The core characteristic of LCF proof systems is the reduction of proofs to primitive inference steps in a formal logical system, albeit without keeping a record of the details of the proof.
The LCF architecture enables high level proof automation to be implemented via a logical kernel capable of ensuring that the resulting proofs are reducible to primitive inference steps.
Trust in the a pure LCF system rests entirely on the logical kernel, which is a modest amount of stable code.

This architecture severely constrains the computational efficiency of deductive methods, and is therefore incompatible with advancement of the Deductive Paradigm to realise its full potential.
Where proof involves computation, a strict adherence to the LCF paradigm would prevent direct computation by hardware and force an elaborate and inefficient evaluation method nonetheless dependent on the correctness of the hardware.
LCF systems usually do allow direct evaluation of some expressions, and in this way diverge from the "pure" LCF paradigm.

In [SPaDE](../docs/tlad001.md#spade), integrity of proof will be a matter of who or what you trust.
Trust is associated with authorities.
All theorems must be signed by the authority who finally derived it, and shown as dependent on the authorities upon which earlier stages in the proof depend.
These complexes of authorities form a partially ordered metric of trust, and the repository will normally be viewed through a filter parameterised by a level of trust which shows only the theorems whose assurance reaches the required level.

The equivalent of the logical kernel of an LCF system will in [SPaDE](../docs/tlad001.md#spade) be one such authority.
Two other kinds of authority will be typical.
The first are mechanisms for direct evaluation of executable specifications.
The second is a general mechanism for inference by the execution of proven derived rules of the logic

These authorities will collaborate to provide a robust framework for formal reasoning and proof development.

## The Role of Metatheory

The reflection principles supported by the core inference mechanisms are intended to substantially transform the structure of high level proof capabilities permitting a systematic implementation of the kinds of support provided in an LCF system by tactics as derived rules.
Though this obviates the need for reduction to primitives, it is nevertheless intended that a mechanism will be included for proof expansion to be made available when specifically requested.

## Deductive Intelligence

Intelligent support for formal engineering in [SPaDE](../docs/tlad001.md#spade) will be provided by  layered alpha-zero like proof automation.
Each theory has a specialist neural net trained by reinforcement learning, to provide heuristics for monte carlo tree search.
Each such [focal](../docs/tlad001.md#focal) proof facility will have access to the specialists for each of its constituent theories (ancestors).

## Concrete Forms

The repository, the core proof capabilities and the intelligent penumbra are all completely abstract, involving no concrete syntax and independent of the stored form of the repository.

Concrete representations of the theories are the responsibility of components of the Knowledge Repository.
Concrete syntax for presenting the theories to human beings will be provided through LLMs, though often human interaction will be less formal.
Of course, in some domains, for example in mathematics or formal logic, more rigorous and formal presentations may be required.
