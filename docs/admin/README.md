# Administrative Documentation

The [SPaDE](../tlad001.md#spade) project is intended, en route to its more ambitious goals, to transform engineering design and construction, starting with software development.

It is now clear to me that an important part of that is project management and administration, which will need to continuously evolve as the capabilities of AI systems evolve, and their role becomes more substantial.

Because of the shifting balance between human and AI contributions, it is preferable to document roles in ways which are agnostic as to whether the role is filled by a human or an AI system.

Agents (including Grok Build) should take in **this directory**, via this README, rather than treating `AGENTS.md` as the project methods manual. `AGENTS.md` is only Grok-specific (and similar) advice. Worktrees, edit scope, commit, and merge to `main` are in [ampd004.md](ampd004.md) and [ampd005.md](ampd005.md). Document placement is in [amms001.md](amms001.md).

This documentation falls into the following categories:

- **[Methods, and standards](#methods-and-standards)**
- **[Process or procedure descriptions](#process-or-procedure-descriptions)**
- **[Plans and strategies](#plans-and-strategies)**
- **[Testing and evaluation](#testing-and-evaluation)**
- **[Task descriptions](#task-descriptions)**
- **[Chat logs](#chat-logs)**
- **[Code and scripts](#code-and-scripts)**

## Methods, and standards

- [amms001.md](amms001.md) Project Structure and Documentation Policy (including: subsystem-specific architecture/design/implementation in the subsystem directory; `docs/` only for whole-system or cross-subsystem material)
- [amms002.md](amms002.md) Roles, Responsibilities, Tasks
- [amms003.md](amms003.md) Workflows
- [amms004.md](amms004.md) Collaborative Guidelines
- [amms005.md](amms005.md) Guidance for AI Contributions
- [amms006.md](amms006.md) Glossary Link Maintenance
- [amms007.md](amms007.md) Glossary Augmentation Procedure
- [amms008.md](amms008.md) LLM Wiki, in progress and not authoritative

## Process or procedure descriptions

- ~~[ampd001.md](ampd001.md)~~ Using GitHub Copilot Agent with SPaDE
- ~~[ampd002.md](ampd002.md)~~ Process for Copilot in completing code and test assignments
- [ampd003.md](ampd003.md) Conversational Documentation Development Procedure
- [ampd004.md](ampd004.md) Branches, worktrees, and sessions
- [ampd005.md](ampd005.md) Independent review: Grok authors, Copilot reviews; PRs into `main`; later LLM-evaluation questions
- ~~[ampd007.md](ampd007.md)~~ Glossary Augmentation Procedure
- [ampd008.md](ampd008.md) Copilot Delegation Procedure with Task Documents

## Plans and strategies

- [ampl001.md](ampl001.md) [SPaDE](../tlad001.md#spade) Project Action Plan
- [ampl002.md](ampl002.md) Prototyping Strategy
- [ampl003.md](ampl003.md) Project Management
- [ampl004.md](ampl004.md) SPaDE Development Strategy
- [ampl005.md](ampl005.md) Immediate plan: Grok Build transition

## Testing and evaluation

Not yet a method. Questions about evaluating SPaDE as a tool *for* LLMs (MCP clients, frozen prompts, independence from the authoring agent) are listed at the end of [ampd005.md](ampd005.md).

## Task Descriptions

- [amtd001.md](amtd001.md) Task Description for Review of Hyperlinks in Project Documentation
- [amtd002.md](amtd002.md) Task Description for Linking Project Documentation to the [SPaDE](../tlad001.md#spade) Glossary
- [amtd003.md](amtd003.md) Task Description for Augmentation of the [SPaDE](../tlad001.md#spade) Glossary
- [amtd004.md](amtd004.md) Task Description for Implementation of Glossary Automation Scripts

## Chat Logs

- [amcl001.md](amcl001.md) Chat Log: Conversational Documentation Development Procedure

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
