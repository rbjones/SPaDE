# Strategy and Plan for Top-Level Philosophy and Architecture Documentation

This document was created initially by github copilot and was to have been progressed by copilot guided by a chat of which the log is [tlcl001.md](tlcl001.md).

After some intial discussion, I moved elsewhere leaving it hanging, and I am now returning to the topic intending to revise the top level myself see what copilot has to say about it and perhaps get copilot to contrubute at lower levels.
My best hope at the moment is that copilot may be able to do detailed design and coding, and we'll see whether it can do any of the higher level design.

## Sketch of Present Thinking

I am looking for a clean and concise exposure of the rationale and strategy for the project, and the architecture which emerges from that, in a way which is accessible to a wide audience, and which can be used as a reference for the more detailed documentation of the various subsystems.

I cannot see how to properly expose the rationale without some autobiographical elements, but I will try to keep those to a minimum, and to focus on the progression of the key ideas in a way which is abstracted away from any unnecessary personal detail.
I already made an attempt at that in [tlpl001.md](tlpl001.md), but that attempt seems to me to be a bit too much of a personal narrative, and I want to try to make it more concise and more focused on the key ideas.
I propose to leave that longer account intact and attempt something more compact in a new document.

There are two sides to the project, philosophy and engineering, and it is likely that readers will be more interested in one than the other, so I will try to keep the two sides as separate as possible, while still showing how they relate to each other.
This is possibly easier for the philosophical side, though that will probably be inextricable from some of the technical material relating to the logical foundations and representation of knowledge.
The engineering can certainly progress quickly to fairly concrete details of the architecture, design and implementation of the various subsystems, the philosophy being relevant primarily to the motivation for the archiecture rather than its details.

At the top level, five documents provide a structure which provides two routes into the project documentation.
There are suitably reworked and expanded (or contracted) versions of the following existing documents:

- the top level [README](README.md) which should link prominently to the other three and give a first account of their roles in the exposition.
- [Background to the Rationale for SPaDE](../docs/tlph009.md), a background document which gives as concise an account as I can muster of the reasoning which lead me to my present conception of the project, possibly linking to a more detailed account of the same.
- [Synthetic Philosophy](../docs/tlph001.md)
- [Deductive Engineering](../docs/tlph002.md)
- [The Purpose of SPaDE](../docs/tlph012.md) and/or [SPaDE Project Aims and Ambitions](../docs/tlph003.md)

This is as far as the plan goes at this stage, further detail will be worked out as I progress with the writing of the top level documents, and will be added to this document as it emerges.

## Some Further Strategic Considerations

I'd like to fit together here (pro-tem) a number of considerations which should inform the planning of progress on SPaDE.

They fall under the following headings:
- Evolutionary Considerations
- RSI and Singularities
- Critical Path Analysis

These are all considered in the light of the purpose of SPaDE to contribute to the proliferation of benign intelligence across the cosmos.

The point of putting them here is not further philosophical exposition.
It is a method for choosing what to do next.
High-level documentation that does not change which work is on the critical path, or which growth rate that work is meant to raise, is not a substitute for that choice.
A progression that is philosophically tidy but too slow will not suffice: on the timescales that matter, it is selected against.

### Evolutionary Considerations

The timescales (billions of years) suggest that evolutionary imperative will have a significant impact on outcomes.
The effect is that at all stages decisions should aim to maximize relevant growth rates, so that we continue to play into those features of intelligent systems which will eventually predominate.

There are multiple relevant evolutionary processes, and clearly the evolution (by design) of the physical infrastructure for transport, and manufacture (replication) are important, but the requirement for benign outcomes is a cultural matter and therefore subject to the more complex dynamics of cultural evolution.

A planning consequence: every substantial piece of work should be identifiable as raising some named growth rate (capability of a singular focus, coverage of a repository, rate of verified design, cultural uptake of norms, and so on).
Work that does not raise a relevant rate, or that raises a rate that cannot predominate, is off the critical path even if it would complete a nicer document hierarchy.

### RSI and Singularities

"The singularity" is usually treated as one event: AI that redesigns AI, hence recursive self-improvement (RSI) and a hyperexponential jump.
That picture is too coarse for planning.

RSI is the application of a capability to the advancement of that same capability.
It can occur at many scopes.
A *singularity* in the sense used here is a point at which such a loop is closed tightly enough that the growth rate of the capability changes qualitatively.
A *singular focus* is the perfect-information core of that loop: a formal theory (or hierarchy of theories) in which the capability is modelled, so that focal methods can drive the self-advancement.

The *focal tower* is the sequence of such foci, each delivering a self-advancing capability that is then used to reach the next.
As one ascends, the capability (or the context in which it must operate) becomes broader.
The lowest singularities can be entirely focal: they concern only the structure of logical systems.
Higher ones have a focal core inside a much larger engineering and cultural problem (physical manufacture, transport, norms).
Those upper levels are not "not SPaDE"; they are the test of whether the lower loops are pointed at the right growth rates.
SPaDE's own engineering, for a long time, lives at the bottom of the tower.

A mathematical singularity (unbounded acceleration) will not occur.
The useful content of the idea is RSI at successive scopes, each raising a growth rate until some other constraint binds.

### Critical Path Analysis

The critical path is the shortest sequence of work that closes the next reachable RSI loop, then the next, up the focal tower.

At each stage the questions are:

1. What is the next singular focus that can actually be closed (capability applied to its own advancement, with a focal core)?
2. What blocking capabilities must exist before that loop can run continuously?
3. What of the present work does not lie on that path?

Coarse levels of the tower, from the bottom, for planning (not a complete ontology):

1. **Logical / metatheoretic.** Formal deduction, then reasoning *about* deduction: derived rules, reflection, heuristics over contexts. The first singularity is here. It is fully focal.
2. **Software of the reasoner.** Using (1) to re-engineer the systems that implement (1). Still digital, still largely focal once the software is modelled.
3. **Physical engineering.** Formal models of artifacts and of the infrastructure that designs and makes them. Empirical knowledge enters. Self-improvement is constrained by fabs, supply, and existing industry.
4. **Unconstrained embodiment / proliferation.** Design of systems that grow in situ in environments that lack Earth's infrastructure, including transport. Normative questions (what is to be proliferated, and why it should be benign) bind here; they also bind earlier as cultural evolution, but they cannot be the first engineering loop.

SPaDE at the highest level is the attempt to get (1) closed and running continuously, in a repository and delivery path that can later carry (2)–(4) without a change of philosophical destination.
The bootstrap problem is exactly: reach a state in which deductive intelligence can work continuously on the first singular focus.
Until that loop exists, further elaboration of higher levels does not raise the growth rate that must predominate first.

The onion of subsystems (knowledge repository, then kernel, then deductive intelligence, delivered through MCP) is the engineering decomposition of that bootstrap, not a second strategy.
Philosophy and architecture documentation is on the critical path only insofar as it is required to keep the next loop pointed at the right rate — including the cultural/normative rate, which otherwise drops out of an engineering-only climb.

This sketch is for planning.
How it should be connected to the existing focal-tower, first-focus, and action-plan documents is deferred until the structure here is stable enough to use.


