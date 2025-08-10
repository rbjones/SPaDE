# Deductive Kernel Development Plan

The following approach is proposed to developing a new deductive kernel for HOL, making full use of the existing HOL system.

Note that though I have separate directories for the deductive kernel and the knowledge repository, its not really possible to develop these separately, even though the formal specifications can be more or less independent.
So I'm starting this knowing that the kr APIs are likely to get interlocked with it pretty soon

One reason for this is that the intention is to use HOL to bootstrap the new logical kernel, by creating a knowledge base which contains correctness results for derived rules without which the kernal would be very rudimentary.
That knowledge base would then be viewed through the kr APIs to effectively convert it from a ProofPower theory hierarchy to a SPaDE knowledge base.
So here's how I think this might go.

1. Initial Metatheory Development

(a) Using ProofPower HOL, load the formal specifications of ProofPower HOL from the spc001-5 series which is issed as part of ProofPower source releases.
(b) With those specification in context, define the criteria for a logically conservative derived rule.
(c) Specify elementary inference rules from which the more complex rules in the existing kernel specification might be derived.
(d) Prove that they are OK
(e) using those definitions, redefine the more powerfull rules currently in the ProofPower kernel.
Prove the correctness of those rules.
2. Add a rule to permit an external engine to execute ProofPower HOL definitions and return a theorem asserting the result of a computation.
3. Add a rule admitting the application of a proven derived inference rule.
4. Now we have to go back and rework the specifications so that they are all executable.
5. Specify and implement the HOL function execution engine.