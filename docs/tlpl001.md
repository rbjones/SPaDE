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
- [Background to the Rationale for SPaDE](docs/tlph009.md), a background document which gives as concise an account as I can muster of the reasoning which lead me to my present conception of the project, possibly linking to a more detailed account of the same.
- [Synthetic Philosophy](docs/tlph001.md)
- [Deductive Engineering](docs/tlph002.md)
- [The Purpose of SPaDE](docs/tlph012.md) and/or [SPaDE Project Aims and Ambitions](docs/tlph003.md)

This is as far as the plan goes at this stage, further detail will be worked out as I progress with the writing of the top level documents, and will be added to this document as it emerges.
