# SPaDE Project Philosophy, Architecture, and Administration

This directory covers those aspects of the SPaDE project which are not specific to any one component, primarily concerning philosophical background, architecture, and administrative matters.

Philosophy and architecure are intertwined and therefore begin toether with:

[**Philosophy and Architecture**]tlph006.md](tlph006.md)

Adminstrative matters are covered in the:

[**Admin Directory**](admin/README.md)

We also have:

 [**The SPaDE glossary**](tlad001.md)

 covering special terminology and abuse of language.
 Linked to relevant parts of the project documentation make this an alternate way of exploring the project.

*The following materials are retained here while I ensure that they are covered adequately in the other documents.*

The SPaDE project has the following main objectives:

- To argue that the abstract representation of the logic known
as *Cambridge HOL* is suitable as a general representation form for declarative knowledge irrespective of what language or coding it may have been presented or stored in.

- To articulate a conception of a
[deductive paradigm shift](tlph005.md) which,
with the benefit of effective automation only possible through AI
will transform the exploitation of declarative knowledge
from computation processes of uncertain effect to
formally verified computation yielding unambiguous and reliable truths.

- To specify APIs and protocols for access to a distrbuted shared repository of knowledge.
The abstract form of knowledge is that of the abstract syntax of HOL and the abstract semantics is also that of HOL.
The concrete forms may be diverse, and concrete semantics addresses the material world by giving concrete interpretation for various abstract domains.
Arbitrary sources of data can be viewed as incorporated into this scheme, wither by treating it as data (i.e. assigning explicit values to new names), or by semantic embeddings, shallow or deep.

- To build an abstract inference engine supporting those processes
in a manner independent of the concrete syntax or stored form
of the knowledge which forms the logical context for the inference.

## Documentation Structure

The documentation is organized into several directories, each serving a specific purpose:

### [admin/README.md](admin/README.md) Admin Documentation

Project management, collaboration framework, and planning documents:

- [Issues and Gaps](admin/ISSUES.md) - Comprehensive analysis of project issues

- [Collaboration Framework](admin/) - Human/AI collaboration documentation

### Philosophy and Architecture

Core philosophical concepts and foundations:

- [tlph001.md](tlph001.md) - A STEM Fantasy and Ethical Consequence. A speculation on the distant future providing a rationale for project
- [tlph002.md](tlph002.md) - Synthetic Philosophy
- [Philosophical Preliminaries](tlph006.md) - Basic philosophical approach
- [Deductive Paradigm](tlph005.md) - The paradigm shift concept
- [Epistemological Stack](tlph003.md)
- [Focal Engineering](tlph004.md)

### [Knowledge Repository](../kr/README.md)

- [Knowledge Repository](../kr/KnowledgeRepo.md) - Repository architecture

### [Deductive Kernel](../dk/README.md)

- [Deductive Kernel](../dk/kernel.md) - Kernel design and implementation

## Collaboration Framework

This project emphasizes human/AI collaboration as essential to its success. The collaboration framework is documented in the [admin directory](admin/), including:

## Contributing

See the [admin documentation](admin/) for collaboration guidelines and project management procedures.
