# The SPaDE Deductive Kernel

This is a first sketch of the deductive kernel for SPaDE.
The deductive kernel is so called because its role is broadly similar to that of the kernel of an interactive theorem prover, responsible for ensuring the integrity of the deductive system, though the approach to that end is quite different.

In an LCF system, the kernel implements an abstract data type of theorems monopolising the ways in which values of that type can be created and ensuring that any computation of a valur of type theorem perfectly shadows (without exhibiting or preserving) a formal proof in the underlying logic.
This makes it safe for users to program advanced theorem proving algorithms without any risk of compromising the integrity of proof checking.

In SPaDE the kernel supports primitive inference rules and more complex derived inference rules in a different way, making use of digital signatures to allow a user to select a level of authentication appropriate to his application, and to make use an open ended variety of software and/or hardware support in the application of deductive methods.

SPaDE enables the use of any authority to undertake and endorse deductive reasoning, requiring such an authority to digitally sign the theorems it endorses and enabling users to select, using a heirarchy of authorities, the level of authentication they require for the theorems they use in their applications.

These same mechanisms also enable real-world interaction, effecting actions in the world and obtaining assurance of their completion in a way intended to dovetail with the use of smart contracts on blockchains, maximising the assurance that real world contracts will achieve their intended effects.
