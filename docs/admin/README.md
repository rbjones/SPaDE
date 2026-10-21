# Administrative Documentation

This documentation falls into the following categories:

- **[Code and scripts](#code-and-scripts)**
- **[Chat Logs](#chat-logs)**
- **[Methods and standards](#methods-and-standards)**
- **[Process or procedure descriptions](#process-or-procedure-descriptions)**
- **[Plans and strategies](#plans-and-strategies)**
- **[Task Descriptions](#task-descriptions)**
- **[Testing and evaluation](#testing-and-evaluation)**

## Methods and standards

- [amms001.md](amms001.md) Project Structure and Documentation Policy (including: subsystem-specific architecture/design/implementation in the subsystem directory; `docs/` only for whole-system or cross-subsystem material)
- [amms002.md](amms002.md) Roles, Responsibilities, Tasks
- [amms003.md](amms003.md) Workflows
- [amms004.md](amms004.md) Collaborative Guidelines
- [amms005.md](amms005.md) Guidance for AI Contributions
- [amms006.md](amms006.md) Glossary Link Maintenance
- [amms007.md](amms007.md) Glossary Augmentation Procedure (historic, pro-tem)
- ~~[amms008.md](amms008.md) LLM Wiki, in progress and not authoritative~~
- [amms009.md](amms009.md) Agentic development team: roles and where work is written
- [amms010.md](amms010.md) DGX Spark software baseline
- [amms011.md](amms011.md) First local role cards: project manager, architect, philosopher
- [amms012.md](amms012.md) Method for Writing ProofPower HOL Specifications

## Process or procedure descriptions

- [ampd001.md](ampd001.md) GitHub-scheduled Copilot agent; tests in the SPaDE container
- [ampd002.md](ampd002.md) Process for Copilot completing code and test assignments
- ~~[ampd003.md](ampd003.md)~~ Conversational Documentation Development Procedure
- [ampd004.md](ampd004.md) Task branches, worktrees, and sessions
- [ampd005.md](ampd005.md) Independent review of pull requests into `main`; later LLM-evaluation questions
- [ampd007.md](ampd007.md) Glossary Augmentation Procedure
- [ampd008.md](ampd008.md) Copilot Delegation Procedure with Task Documents
- [ampd009.md](ampd009.md) Commissioning work on the Spark: local agents, cloud models, review, GitHub Issues
- [ampd010.md](ampd010.md) Local agent task execution
- [ampd011.md](ampd011.md) Task Assignment Procedure for Local LLMs
- [ampd012.md](ampd012.md) Procedure for Writing Specifications in ProofPower HOL

## Plans and strategies

- [ampl001.md](ampl001.md) [SPaDE](../tlad001.md#spade) Project Action Plan
- [ampl002.md](ampl002.md) Prototyping Strategy
- [ampl003.md](ampl003.md) Project Management
- [ampl004.md](ampl004.md) SPaDE Development Strategy
- [ampl005.md](ampl005.md) Immediate plan: Grok Build transition
- [ampl006.md](ampl006.md) Development on the DGX Spark: parallel preparation, architectural evaluation, checking HOL
- [ampl007.md](ampl007.md) Fine-tuning for specifications and the MCP interface

## Testing and evaluation

Not yet a method. Questions about evaluating SPaDE as a tool *for* LLMs (MCP clients, frozen prompts, independence from the authoring agent) are listed at the end of [ampd005.md](ampd005.md).

## Task Descriptions

- [amtd001.md](amtd001.md) Task Description for Review of Hyperlinks in Project Documentation
- [amtd002.md](amtd002.md) Task Description for Linking Project Documentation to the [SPaDE](../tlad001.md#spade) Glossary
- [amtd003.md](amtd003.md) Task Description for Augmentation of the [SPaDE](../tlad001.md#spade) Glossary
- [amtd004.md](amtd004.md) Task Description for Implementation of Glossary Automation Scripts
- [amtd005.md](amtd005.md) Task Description — Execute Glossary Augmentation Process

## Chat Logs

- [amcl001.md](amcl001.md) Chat Log: Conversational Documentation Development Procedure
- [amcl002.md](amcl002.md) Grok web discussion links formerly listed under `drafts/`
- [amcl003.md](amcl003.md) Session record: agentic team on the DGX Spark

## Code and Scripts

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
