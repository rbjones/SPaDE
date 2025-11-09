# Administrative Documentation

The [SPaDE](../tlad001.md#spade) project is intended, en route to its more ambitious goals, to transform engineering design and construction, starting with sofware development.

It is now clear to me that an important part of that is project management and administration, which will need to continuously evolve as the capabilities of AI systems evolve, and their role becomes more substantial.

Because of the shifting balance between human and AI contributions, it is intended to document roles in ways which are agnostic as to whether the role is filled by a human or an AI system.

This documentation falls into the following categories:

- **[Methods, processes and standards]**(#methods-processes-and-standards-(amms))(amms)
- **[Plans and strategies]**(#plans-and-strategies-(ampl))(ampl)
- **[Testing and evaluation]**(#testing-and-evaluation-(amte))(amte)
- **[Task descriptions]**(#task-descriptions-(amtd))(amtd)
- **[Code and scripts]**(#code-and-scripts-(amcd))(amcd)

## Methods, Processes and Standards (amms)

### Project Management

Interaction with the project will be managed through GitHub Projects.
This is a facility which is still evolving, and I will update this documentation as I learn how to use it effectively.

A github project has been set up for [SPaDE](../tlad001.md#spade), so the terminology used here when discussing plans will reflect that useed by the github project management system and will evolve with it
All activities in such a project have to be set up as "issues" and dependencies between these issues are registered as "blocks".
In this discussion I will use the term "task" to refer to an issue which is a significant piece of work, and "subtask" to refer to a smaller piece of work which is part of a larger task.
Subtasks are registered as "child" issues, the task being the "parent" issue.
So far the [SPaDE](../tlad001.md#spade) "project" covers only the first MCP server prototype.

I have found it difficult to see the dependencies between tasks, with the facilities available and have therefore adopted the practice of prefacing each task title with a number indicating its place in the sequence of tasks as well as the parent/child relationships.
Thus (for example) task 3.2 is the second subtask of task 3.
The sequences of tasks and subtasks will be documented in the project management system.

Meanwhile I have a top level planning rumination [ampl001.md](ampl001.md) which will be reviewed to address a strategy plan not yet reflected in the project management system.

- [amms001.md](amms001.md) Project Structure and Documentation Policy
- [amms002.md](amms002.md) Roles, Responsibilities, Tasks
- [amms003.md](amms003.md) Workflows
- [amms004.md](amms004.md) Collaborative Guidelines
- [amms005.md](amms005.md) Guidance for AI Contributions
- [amms006.md](amms006.md) Glossary Link Maintenance
- [amms007.md](amms007.md) Glossary Augmentation Procedure

## Process or procedure descriptions (ampd)

- [ampd001.md](ampd001.md) Using GitHub Copilot Agent with SPaDE - Process for assigning code-and-test tasks to Copilot agents

## Plans and strategies (ampl)

- [SPaDE](../tlad001.md#spade) Project Action Plan [ampl001.md](ampl001.md)
- Prototyping Strategy [ampl002.md](ampl002.md)

## Testing and evaluation (amte)

## Task Descriptions (amtd)

- [amtd001.md](amtd001.md) Task Description for Review of Hyperlinks in Project Documentation
- [amtd002.md](amtd002.md) Task Description for Linking Project Documentation to the [SPaDE](../tlad001.md#spade) Glossary
- [amtd003.md](amtd003.md) Task Description for Augmentation of the [SPaDE](../tlad001.md#spade) Glossary
- [amtd004.md](amtd004.md) Task Description for Implementation of Glossary Automation Scripts

## Code and Scripts (amcd)

- [amcd001.py](amcd001.py) - Script for adding glossary links to documentation
  - Dynamically loads terms from glossary
  - Supports incremental operation with `--since` parameter
  - Generates review reports
  - Handles file filtering and dry-run mode
- [amcd002.py](amcd002.py) - Script for extracting terms from glossary
  - Parses glossary file to extract all terms and anchors
  - Outputs in multiple formats (python, json, text)
  - Handles term variations and compound terms
  - Used by amcd001.py for dynamic term loading
- [amcd003.py](amcd003.py) - Script for discovering potential glossary terms
  - Scans documentation for technical terminology
  - Filters by frequency and importance
  - Outputs candidate terms with usage contexts
  - Supports glossary augmentation workflow
