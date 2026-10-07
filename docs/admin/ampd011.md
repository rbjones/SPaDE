# AMPD011: Task Assignment Procedure for SPaDE

## Introduction

This procedure it intended to enable maximal application of local LLMs to SPaDE, by providing a standard way of scheduling tasks which is consistent both with human and agentic completion by copilot or local LLMs.

The procedure is under development and is likely to evolve continuously during the early stages of its adoption.

It is not yet in an acceptable state, and will not be good until at least one task has gone through the entire procedure successfully.

The procedure is presented in the following parts:

- [Informal Overview](#informal-overview)
- [Task Definition](#task-definition)
- [Validation of Task Description](#validation-of-task-description)
- [Task Assignment](#task-assignment)
- [Task Execution](#task-execution)
- [Validation and PR](#validation-and-pr)
- [Example Task Document](#example-task-document)
- [Notes](#notes)

## Informal Overview

The basic idea is that tasks will be defined clearly by a specific task definition, to be read in the context of the other SPaDE project standards and procedures, and will be raised as a github issue and appropriately assigned in that issue (not sure how, since we only have one github user account at the moment, probably has to be assigned to the project leader with more specific information in the task description as to what who needs to do it, possibly by citing a role).

It is anticipated that some kind of scheduler will then retrieve the issues ready for progression which can be undertaken by local LLMs and will present them for completion.

Task descriptions are effectively layered, there being an overall standard to task descriptions, more specific task descriptions for particular kinds of task and completely specific task descriptions for individual tasks.
So for example, in addition to the general standards for task descriptions, there are many particular requirements on how specifications in ProofPower HOL are written and checked, and a procedure which details these is referred to by any task which involves writing or modifying such a specification.

Specific task descriptions will be placed in the project directory where the files produced or modified by the task are located.
If the task involves producing a new document, then if possible the number of the document should correspond to the number of the task description.

## Task Definition
- **Document Creation**: Create a task description document in that part of the SPaDE git repo where the work will be undertaken (usually the directory docs, kr, dk, di or mcp)following `docs/admin/amms001.md` naming conventions (e.g., `krtdxxx.md`) describing the objective of the work, the steps necessary to realise that objective and the manner of checking the work, explicitly referring to key documents as needed.
Example:
  ```markdown
  # Task: Recast HOL TERMS for SPaDE

  ## Objective
  Recast HOL TERMS specification from `spc003.pp`/`spc004.pp` into SPaDE's format.

  ## Steps
  1. Extract relevant sections using `grep`.
  2. Define SPaDE equivalents for HOL constructs.
  3. Output plain text with formal specifications.
  ```

## Validation of Task Description
Ensure the document includes:
  - Clear objective
  - Step-by-step instructions
  - Expected output format
  - Dependencies (e.g., files to modify)

## Task Assignment
- **Branch Creation**: scheduler creates a new branch and worktree for this particular taskfrom the relevant area branch (am, kr, dk, di, mcp):
  ```bash
  git checkout -b task-recast-hol-terms
  ```
- **Task Launch**: Use the `task` tool with the document as input:
  ```bash
  task \
    --name recast-hol-terms \
    --agent-type general-purpose \
    --mode background \
    --prompt /home/rbj/git/SPaDE-am/docs/admin/task-recast-hol-terms.md
  ```
- **Worktree Setup**: The local LLM creates a worktree for isolated changes:
  ```bash
  git worktree add ../SPaDE-am-task-recast-hol-terms task-recast-hol-terms
  ```

## Task Execution
- **Autonomous Work**: The local LLM:
  1. Parses the task document
  2. Executes steps (e.g., `grep`, `edit`, `view_range`)
  3. Commits changes with `Co-authored-by` trailer
  4. Pushes results to the branch

## Validation and PR
- **Cloud Agent Review**: The cloud agent:
  1. Verifies task completion via `read_agent`
  2. Runs linters/tests (e.g., `npm run lint`, `make test`)
  3. Uses GitHub MCP to create a PR:
     ```bash
     gh pr create --title "Recast HOL TERMS for SPaDE" --body "See task description in docs/admin/task-recast-hol-terms.md"
     ```
- **PR Requirements**: Ensure the PR includes:
  - Task document reference
  - Code changes
  - Validation results

## Example Task Document
See `docs/admin/task-recast-hol-terms.md` for a template.

## Notes
- **Monitoring**: Use `read_agent` to track task progress.
- **Error Handling**: If the task fails, the cloud agent:
  1. Reviews logs via `read_agent`
  2. Updates the task document
  3. Relaunches the task

This procedure ensures tasks are reproducible, auditable, and aligned with SPaDE's distributed development model.