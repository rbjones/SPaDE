# Inductive Definitions by Enumeration

An important aim in devising a new kernel and deductive engine
for HOL for this (chdkr) project is to appply the deductive capability
to the metatheory necessary to extend and improve
the capabilities of the engine.
This is to be done in the context of an ultraminimal kernel,
which will make the metatheory more tractible and enable the reflexive
self-improvement to come into play as early as possible.

This document sketches the approaches which are currently
being progressed to this problem.

## On The Representation of Inductive Datatypes

In the Cambridge HOL logical foundation system it is normal
wherever possible to introduce theories by conservative extension.
In the case that new types or type constructors are required,
this involves demonstrating that the new types being introduced
are isomorphic to structures which can already be defined in the
context which is to be extended with the new types.
For inductive types, this depends on there being types already
available which are large enough to be closed under the reqhired
constructors for the inductive type.
For example, the simplest such type is the natural nunmbers,
so in order to conservatively introduce the natural numbers
a representative type is required which is close under the
constructors 0 and Suc.

This demands a type with infinitely many members, and so cannot
be done without an axiom of infinity
(and as it happens, is simple enough to use for the natural numbers
without using inductive datatype support).
More elaborate inductive types require larger representation types
in order to get a fixed point.

The universality of the proposed system therefore depends upon
the possibility of strengthening through axiomatic princples
similar to large cardinal axioms in set theory.

In the context of HOL, this strengthening does not require an axiomatic
set theory, but can be realised by strong axioms of infinity over
the `individuals'.
Since we have the axiom of choice, we can prove that every type has a
strict initial well-ordering and is isomorphic to an initial segment
of the ordinals.
We therefore propose:

1. That instead of the primitive type IND, we have a
primitive type-constructor ORD, with one type parameter.
The type parameter is needed because these types will be used
to enumerate inductive datatypes
(and hence provide representatives of the types to be introduced),
and if polymorphic datatypes are to be supported
will therefore have to be polymorphic.

2. The ORD type constructor will create a type which of which
the ordering of the parameter type is an initial segment
of the ordering of the constructed type and has
a strict supremum in that type.

3. Strong axioms of infinity will then make stronger claims
about the cardinality of the contructed type.
To support a good range of inductive data types,
and match the strength of the Clean type theory a strong infinity, 
asserting that every ordinal ie less than some inaccessible,
will suffice.

This enables us to easily construct a type sufficient for
the representation of any inductive data type in the following way.

By way of illustration let us consider a polymorphic type of lists.
The constructors for this type might be:

[]:′a LIST
Cons: ′a ×′a LIST → ′a LIST

In which 'a is a type variable and × is the ordered pair
type constructor.
A composite de-construction function might therefore have the following type:

'a LIST → ONE + ('a × 'a LIST)

THe idea is to enumerate the inductive type in increasing order of rank
with the elements of each rank ordered by choice of
an arbitrary initial well-ordering.
To do this we need a well-ordering of sufficient cardinality,
and I know no simple rule for chosing such a type,
not least because there are some inductive definitions which have
no fixed point, but for which an enumeration may nevertheless be sought.
(The proposed mechanisms could, for example, be used to construct
a type of sets supporting a higher order variant of ZFC by iterating
the power set constructor, which would be useful but would exhaust
any chosen representation type, however large,
without reaching a terminus).

The only guidance I can suggest at this point is that for
monomorphic types (BOOL)ORD is most likely to be enough,
unless the constructions themselves invole the ORD type constructor.


(ONE + ('a × 'a LIST)) ORD

and a composite projection from that type would have the type:

(ONE + ('a × 'a LIST)) ORD  → ONE + ('a × 'a LIST)

in which ORD is the type constructor carrying
the axiom of strong infinity.