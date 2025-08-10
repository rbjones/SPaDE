# SPaDE Project Documentation

The SPaDE project has the following main objectives:

* To argue that the abstract representation of the logic known
as _Cambridge HOL_ is suitable as a general representation form for declarative knowledge irrespective of what language or coding it may have been presented or stored in.

* To articulate a conception of a
[deductive paradigm shift](DeductiveParadigm) which,
with the benefit of effective automation only possible through AI
will transform the exploitation of declarative knowledge
from computation processes of uncertain effect to
formally verified computation yielding unambiguous and reliable truths.

* To specify APIs and protocols for access to a distrbuted shared repository of knowledge of which the abstract form is the abstract syntax of HOL but the concrete forms diverse, enabling information in any form to be accessed as an element of that distributed repository.

* To build an abstract inference engine supporting those processes
in a manner independent of the concrete syntax or stored form
of the knowledge establishing the context for the inference.

## Documentation Structure

### [Admin Documentation](admin/README.md)
Project management, collaboration framework, and planning documents:
- [Issues and Gaps](admin/ISSUES.md) - Comprehensive analysis of project issues
- [Project Structure](admin/PROJECT_STRUCTURE.md) - Proposed enhanced organization
- [Action Plan](admin/ACTION_PLAN.md) - Detailed implementation roadmap
- [Collaboration Framework](admin/) - Human/AI collaboration documentation

### [Philosophical Foundations](philosophy/)
Core philosophical concepts and foundations:
- [Philosophical Preliminaries](PhilosophicalPreliminaries.md) - Basic philosophical approach
- [Deductive Paradigm](DeductiveParadigm.md) - The paradigm shift concept

### [Architecture](architecture/)
System architecture and design:
- [Knowledge Repository](kr/KnowledgeRepo.md) - Repository architecture
- [Deductive Kernel](dk/kernel.md) - Kernel design and implementation

### [Specifications](specifications/)
Formal specifications and technical details:
- [Cambridge HOL Syntax](specifications/) - Formal syntax definitions
- [Type System](specifications/) - Type system specifications
- [Inference Rules](specifications/) - Logical inference rules

### [Papers](papers/)
Academic papers and publications:
- [CHDKR Paper](chdkrpaper.tex) - Main technical paper

## Theory Source Integration

Rather than creating our own examples, the project focuses on:
- **Established theory sources**: Using existing mathematical and logical theories
- **KR interfaces**: Accessing rich theory repositories through generic interfaces
- **AI training**: Leveraging established theories for training AI algorithms
- **Real-world applications**: Working with actual theory bases rather than simplified examples

## Collaboration Framework

This project emphasizes human/AI collaboration as essential to its success. The collaboration framework is documented in the [admin directory](admin/), including:

- **Roles and Responsibilities**: Bertie (philosopher/architect) and Alan (high-bandwidth contributor)
- **Collaboration Methods**: Standards and approaches for effective collaboration
- **Workflows**: Specific processes for different types of work
- **Quality Assurance**: Review and validation procedures

## Development Status

**Current Phase**: Foundation and structure setup
- [x] Initial project analysis completed
- [x] Collaboration framework established
- [ ] Core terminology defined
- [ ] Philosophical foundation completed
- [ ] Formal specifications developed
- [ ] Theory source integration strategy defined

## Contributing

See the [admin documentation](admin/) for collaboration guidelines and project management procedures.
