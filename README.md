# Cambridge HOL for Declarative Knowledge Repository

Yes, not a good name, but I timed out on my search for a better one.

The purpose of this project is to argue the case for,
and build infrastructure to support,
the idea that a particular variant of classical Higher Order Logic
is suitable for the representation and manipulation
of all declarative knowledge.

The variant in question is called "Cambridge HOL"
since it was devised by Michael Gordon and associates
at the University of Cambridge for use in
the interactive theorem prover then called "Cambridge HOL".

For the purposes of this project, it is the abstract structure of
the Cambridge HOL logical system which is adopted
and promoted for a broader role.
The project separates out that abstract representation and logical system
from its concrete forms, concrete syntax and physical storage formats,
allowing for a diversity of front ends, using the same underlying
abstract representation, for a diversity of declarative languages
or for AI mediated dialogue yielding structures reflecting
user requirements, perhaps with no explicit textual renderings.

The divorce from the concrete will be achieved through the provision
of APIs and protocols supporting both front ends and back ends.
Progression of the project will depend on there being such front ends
and back ends, but these will be development tools and exemplars
rather than products.
The main aim of this project is to create a deductive intelligence
which will reliably and efficiently work deductively within any logical
context rendered through the defined interfaces.

There are two main subsystems which will be addressed by the project.
The logical structure of the knowledge repository,
and the core deductive capabilities which enable applications to 
process and apply the knowledge in the repository.
These core capabilities are intended to contribute
to a deductive paradigm shift in which information processing in general 
is augmented by reliable and efficient formal rigour. 

The development of the core deductive capabilities will be focused
on certain areas which will ultimately contribute to the continued
development of the broader applications.
That first focus will be on formally rigorous design and
build capabilities.
Within that a medium term focus will be on AI supported
software engineering, and in the first instance the logical kernel
will be re-engineered to facilitate the development of
its own metatheory and the verification of derived rules
which can then be efficiently applied in derivations.
For such purposes, programming languages will be represented
by the abstract HOL syntax, and a significant adaptation
of the LCF paradigm now widely used in interactive proof tools
is envisaged, allowing that tactics which have been proven to be sound
can shortcut the requirement for detailed verification of
low level proof steps.
The possibility of doing this permits simplicity in the logical kernel
to be taken to its limits, but demands that the development of the theory
hierarchy focus on the machinery for metatheory.

The structure of the repo at this point falls into two directories:

* [docs](docs/README.md).
    This is the main documentation covering all aspects of the description of the project including formal specifications.

* [retro](retro/README.md)
    This is a directory which contains material from previous projects
    and work preliminary to the specification and implementation of the new project which makes use of some of that previous material, and must be done in that context in the first instance.

```
ⓈHOLCONST
│ $⦏≤⋎s⦎ : 'a ℙ → 'b ℙ → BOOL
├──────
│ ∀ A B⦁ A ≤⋎s B ⇔ ∃f⦁
│	∀x y⦁ x ∈ A ∧ y ∈ A ⇒ f x ∈ B ∧ f y ∈ B ∧ (f x = f y ⇒ x = y)
■
```
