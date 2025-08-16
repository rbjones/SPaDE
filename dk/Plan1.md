# Deductive Kernel Development Plan

The following approach is proposed to developing a new deductive kernel for HOL, making full use of the existing HOL system.
This is not the whole story, just some opening gambits.

Note that though I have separate directories for the deductive kernel and the knowledge repository, its not really possible to develop these separately, even though the formal specifications can be more or less independent.
So I'm starting this knowing that the kr APIs are likely to get interlocked with it pretty soon.

There is no intention under this project to develop front ends for any language, not even HOL.
So this creates awkwardness in how to write and process the specifications, which will all be in HOL and will also constitute an implementation.
Three major phases in this will be as follows:

1. Specifications are written in ProofPower HOL and create theories in ProofPower.
   This will be an iterative transformation of the existing formal specifications by Rob Arthan until a satisfactory new kernel specification is reached which is provably the same derivability relation.

2. The resulting ProofPower theories are then exported from ProofPower to create a knowledge repository.
   It is intended that the first implementation of the kernel will be as an HOL interpreter which opens the repository and executes the kernel specification in it.
   This will probably be written in SML using ProofPower.

3. Then we look for ways of implementing the kernel without using ProofPower.
   At this point this is an open book, but since the next stage is the AI proof automation, it might be a good idea to go for a language convenient for doing things with neural nets, perhaps python.
   This is a pretty small program, and it should be implementable in a simple subset of the chosen language, for which an embedding into HOL is straightforward.
   We can then rewrite or augment the formal specification of the kernel to use that embedded fragment of an executable language and a simpler bootstrap would be possible.

This is still sketchy speculation, the following "plan" addressed only the early stages in which we approach a formal specification of the kernel without considering the implementation and bootstrapping problems.

[some repetition here]
The intention is to use HOL to bootstrap the new logical kernel, by creating a knowledge base which contains correctness results for derived rules without which the kernel would be very rudimentary.
That knowledge base would then be viewed through the kr APIs to effectively convert it from a ProofPower theory hierarchy to a SPaDE knowledge base.
So here's how I think this might go.

1. Initial Metatheory Development
  a. Using ProofPower HOL, load the formal specifications of ProofPower HOL from the spc001-5 series which is issued as part of ProofPower source releases.
  b. With those specification in context, define the criteria for a logically conservative derived rule.
  c. Specify elementary inference rules from which the more complex rules in the existing kernel specification might be derived.
  d. Prove that they are OK
  e. using those definitions, redefine the more powerful rules currently in the ProofPower kernel.
  f. Prove the correctness of those rules.
2. Add a rule to permit an external engine to execute ProofPower HOL definitions and return a theorem asserting the result of a computation.
3. Add a rule admitting the application of a proven derived inference rule.
4. Now we have to go back and rework the specifications so that they are all executable.
5. Specify and implement the HOL function execution engine.
