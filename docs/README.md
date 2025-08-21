# SPaDE Project Documentation

The SPaDE project has the following main objectives:

* To argue that the abstract representation of the logic known
as _Cambridge HOL_ is suitable as a general representation form for declarative knowledge irrespective of what language or coding it may have been presented or stored in.

* To articulate a conception of a
[deductive paradigm shift](DeductiveParadigm.md) which,
with the benefit of effective automation only possible through AI
will transform the exploitation of declarative knowledge
from computation processes of uncertain effect to
formally verified computation yielding unambiguous and reliable truths.

* To specify APIs and protocols for access to a distrbuted shared repository of knowledge.
The abstract form of knowledge is that of the abstract syntax of HOL and the abstract semantics is also that of HOL.
The concrete forms may be diverse, and concrete semantics addresses the material world by giving concrete interpretation for various abstract domains.
Arbitrary sources of data can be viewed as incorporated into this scheme, wither by treating it as data (i.e. assigning explicit values to new names), or by semantic embeddings, shallow or deep.

* To build an abstract inference engine supporting those processes
in a manner independent of the concrete syntax or stored form
of the knowledge which forms the logical context for the inference.

## Documentation Structure

The documentation is organized into several directories, each serving a specific purpose:

### [Admin Documentation](admin/README.md)

Project management, collaboration framework, and planning documents:

* [Issues and Gaps](admin/ISSUES.md) - Comprehensive analysis of project issues

* [Collaboration Framework](admin/) - Human/AI collaboration documentation

### Philosophy and Architecture

Core philosophical concepts and foundations:

* [A STEM Fantasy](STEMFantasy.md) - a speculation on the distant future providing a rationale for project
* [Philosophical Preliminaries](PhilosophicalPreliminaries.md) - Basic philosophical approach
* [Synthetic Philosophy](SyntheticPhilosophy.md)
* [Deductive Paradigm](DeductiveParadigm.md) - The paradigm shift concept
* [Epistemological Stack](EpistemologicalStack.md)
* [Focal Engineering](FocalEngineering.md)

### [Knowledge Repository](kr/README.md/)

* [Knowledge Repository](kr/KnowledgeRepo.md) - Repository architecture

### [Deductive Kernel](dk/README.md)

* [Deductive Kernel](dk/kernel.md) - Kernel design and implementation

## Collaboration Framework

This project emphasizes human/AI collaboration as essential to its success. The collaboration framework is documented in the [admin directory](admin/), including:

* **Roles and Responsibilities**: Bertie (philosopher/architect) and Alan (high-bandwidth contributor)
* **Collaboration Methods**: Standards and approaches for effective collaboration
* **Workflows**: Specific processes for different types of work
* **Quality Assurance**: Review and validation procedures

## Contributing

See the [admin documentation](admin/) for collaboration guidelines and project management procedures.
