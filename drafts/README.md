# Work in Progress

The account of SPaDE in this repository is a work in progress, and is very incomplete.
The more philosophical aspects will continue to evolve for as long as anyone cares to work on them.
In order to make progress on the more practical aspects of the project, it is necessary to focus on those aspects of the project which are critical to the implementation of the SPaDE MCP server, but the contribution of AI to all aspects of the project is crucial, and can only be undertaken effectively if the philosophical and architectural rationale for SPaDE is well articulated and intelligible to the AI systems contributing to the project.

There is no part of the documentation which could not be improved, and there are many parts which are very incomplete, but focus is essential, and this document is a guide to those parts of SPaDE which are currently being progressed, and to the extent that AI is able to contribute idependently to SPaDE, provides some guidance on where a contribution might be most valuable.

The areas of focus are determined by a strategy which is driven by the desire to make effective AI contributions to the project possible and pervasive.
As things stand, the least difficult area is at the level of code and test, in the context of detailed design, and the strategy is to document the higher level aspects of the process sufficiently well to enable progressively higher level AI contributions, beginning with detailed design sufficient for code and test, and gradually advancing upwards through architectural design and eventually to the philosophical aspects of SPaDE.

That strategy translates into focus on:

- the purpose of the SPaDE project
- the high level architecture of SPaDE
- the rationale connecting the architecture to the purpose
- the data structures and interfaces of the SPaDE knowledge repository, which is central to the architecture and therefore critical to the implementation of the SPaDE MCP server, and which is also a critical aspect of the philosophical rationale for SPaDE, and therefore a critical aspect of the project as a whole.


This is to provide a space for discussion with LLMs either via github copilot or using the web interface to Grok (which I can use for free rather than pay-per-use via the API in copilot.)
The web interface to Grok has folders which provide a degree of persistence.

The documents will generally be placed in their intended destination, but not linked other than in this drafts folder.

Initially the work under discussion is an attempt at a compact but comprehensive rationale for SPaDE feeding down to architectural and detailed design of the system and its main subsystems.
I'm looking to factor this into a *philosophical* presentation and an *architectural* presentation, each of which leans upon a statement of background representing the belief structures in the context of which the purpose of SPaDe can be understood and the features of SPaDE can be seen as a rational approach to realising that purpose.

The philosophical part is currently in:

- [docs/tlph012.md](../docs/tlph012.md) -The Purpose of SPaDE
- [docs/tlph014.md](../docs/tlph014.md) -The Philosophical Rationale for SPaDE
- [docs/tlph015.md](../docs/tlph015.md) The Evolution of Intelligent Systems

The architectural part is to be found in:

- [docs/tlad009.md](../docs/tlad009.md) Background to The Rationale for SPaDE
- [docs/tlad011.md](../docs/tlad011.md) The Architectural Rationale for SPaDE
