# Admin Meta-Task-Description

## Introduction

This is the top level task description for the administrative aspects of the SPaDE development framework.
This covers all aspects of project management, with a particular focus on ensuring that effective and well documented working practices are in place and evolve to meet the needs of the project and take full advantage of the resources available to the project, particularly in relation to the exploitation of the rapidly evolving capabilities of AI and other advanced technologies.

The SPaDE project is a *reflection first* formal methods support system, and anticpates a future in which development of systems and solutions is wholly or predominantly conducted by intelligent agents which interact using formal structures rather than natural languages.
A first step in that direction is the transfer into a SPaDE native repository of the entire SPaDE project, currently held in a git repo hosted at github.
For that reason, we will continually seek to render substantive content in formal content, though clear communication will for some time continue to depend on the use of natural English.

In addition to providing here links to the task descriptions which properly belong in the admistrative and project management domains, this document will identify and link to the meta-tasks covering each of the main project areas.
Those meta-tasks will be documented in the directory housing the subsystem and will task description number zero in that directory.

The rest of this document is structued as follows:
- Meta-Tasks
- Administrative Tasks

## Meta-Tasks

These meta-tasks correlate with directories in the SPaDE repository, and represent areas of responsibility which will replace the role distinctions previously documented (a comprehensive review of admin documentation is needed to bring it all in line with recent practices and the evolving structure of the project).

The current set of subsystem meta-task documents includes the following:

- amtd000: Admin meta-task-description (this documents)
- [tltd000](../tltd000.md): Philosophy and Architecture meta-task-description
- [krtd000](../../kr/krtd000.md): Knowledge Representation meta-task-description
- [dktd000](../../dk/dktd000.md): Deductive Kernel meta-task-description
- [ditd000](../../di/ditd000.md): Deductive Intelligence meta-task-description
- [mcptd000](../../mcp/mcptd000.md): MCP meta-task-description
- [intd000](../../int/intd000.md): Onboarding meta-task-description
- [outtd000](../../out/outtd000.md): Outreach meta-task-description
§
## Principle Areas for Administrative Advancement

There are at present three main areas where progress is expected in the administrative domain:

- [Admin Documentation](#admin-documentation)
- [Local Software Stack](#local-software-stack)

### Administrative Tasks

At present the administrative documentation in directory `docs/admin` is in a state of transition to better support the concurrent application of agents to the SPaDE development, and to enable full use to be made of local computational resources and capabilities.
This is at present being undertaken interactively by the project leader with assistance grok build and copilot.

A first stage in taking the administrative documentation into the new regime will involve informal articulation of principle areas where advances are needed and the purpose and direction of those changes.
Following such an informal prospectus, we will move to more formality making room for autonomous contrubutions from appropriate agents.

### Admin Documentation

This area covers all categories of documentation in the docs/admin directory, particularly those which govern the way development is conducted throughout SPaDE.

It also addresses the question of how these kinds of documentation can be formalised for use in environments where use of the English language is not necessary or desired.
This begins with trialing the use of YML for structuring administrative documentation.
Despite seeking more formal documentation, so long as people and LLMs are central to the effort English will remain an important tool in clear communication.
SPaDE itself is not expected ever to have non-trivial natural language capabilities, and its use by humans will be mediated by other technologies suited to natual language dialogue.

### Local Software Stack

This area concerns the software environment required for the local development and operation of SPaDE.
The aministrative domain is responsible not merely for documenting the software stack, but also for researching the requirements and for configuring and tuning the software.
In particular it is responsible for chosing open weight LLMs suitable for local use, and for tuning suitable models for tasks important to the development and operation of SPaDE.


## Near Term Priorities for Administrative Work

### Adaptation to enable heirarchical parallel autonomous agentic development

The administrative documentation must be adapted to support a development process in which multiple autonomous agents can operate in parallel, each contributing to different aspects of the project.
This mainly concerns the documentation of tasks so that each agent is clear about what it is to achieve, and other agents are able to assess whether their outputs achieve the required objectives.

### Establishment of a Clear Method for Agentic use of ProofPower HOL

A large part of the early development work involves the development of specifications of SPaDE in ProofPower HOL.
This includes preparing formal proofs, which are necessary in the introduction of some specifications, and important for validating their correctness and enabling their use in further specifications.
For that, a means for agents to work interactively with ProofPower will be necessary, since proof development confined to batch processing would be inefficient.

