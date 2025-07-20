## directory retro/np

This directory began as a copy of the directory src/rbjpub/pp/doc from
the github repo rbjones/www.rbjones.com.
It was the directory used to build the web directory at:
www.rbjones.com/rbjpub/pp/doc
In making the transfer I have deleted the history prior to this project,
most of which can be found on the cited repo. in the unlikely event that
anyone cares.

In the first instance the continuing work in this directory will be
concerned with the formal specification of the logical kernel
around which a deductive intelligence will be built.
This formal specification will be used by the new kernel to develop
its own metatheory so that it can verify derived rules permitting them
to be applied without independent checking (a substantial divergence
from the LCF paradigm followed so far by prior implementations of 
Cambridge HOL.
ProofPower HOL already benefits from a formal specification of the
language and kernel written in HOL by Rob Arthan.
The reasons for the rewrite are that the primitive logical system is
being revised as well as the early staged in the theory heirarchy.

The present plan is that the inference rules should be made as simple
as possible, to be later augmented by derived rules, and that
the development of the theory hierarchy should be oriented to achieving
a general purpose method for the definition of recursive datatypes,
and then using that facility developing the metatheory of
the system itself for use in proving extensions to it.

The changes to the specification of the deductive system will be
extensive, so you may ask in what way this is an implementation of
Cambridge HOL. The answer is that the abstract system underlying
Cambridge HOL defines a recursively enumerable set of
derivability assertions, in each of is expressed the derivability of
a sequnnt from some set of sequents.  The system which will be proposed
will derine that same recursively enumerable set
by somewhat different means.
In addition to that change in the presentation of the abstract
deductive system (Cambridge HOL already has distinct concrete forms
among its impleentations) there is a difference in the core
axiom system which involves a stronger axiom of infinity to facilitate
the scope of the inductive type mechanisms intended.
This does nothing which cannot be done in existing implementations
of Cambridge HOL by adding a further axiom.

The most radical differences to the Kernal consist in the ability
to efficiently evaluate functions defined in HOL, yielding a theorem
expressing the result of the computation,
and the ability to infer from a theorem in the netatheory
(possibly obtained by that means)
a sequent proven to be derivable in context.
