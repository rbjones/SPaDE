## AMDP011: Task Assignment Procedure for Local LLMs via Cloud Frontier LLMs

### Objective
Standardize task assignment to local LLMs (e.g., GitHub Copilot CLI) via cloud frontier LLMs, ensuring reproducibility, traceability, and alignment with SPaDE project standards.

### Procedure

#### 1. Task Definition
- **Document Creation**: Create a task description document following `docs/admin/amms001.md` naming conventions (e.g., `task-<feature>.md`). Example:
  ```markdown
  # Task: Recast HOL TERMS for SPaDE

  ## Objective
  Recast HOL TERMS specification from `spc003.pp`/`spc004.pp` into SPaDE's format.

  ## Steps
  1. Extract relevant sections using `grep`.
  2. Define SPaDE equivalents for HOL constructs.
  3. Output plain text with formal specifications.
  ```
- **Validation**: Ensure the document includes:
  - Clear objective
  - Step-by-step instructions
  - Expected output format
  - Dependencies (e.g., files to modify)

#### 2. Task Assignment
- **Branch Creation**: The cloud agent creates a new branch:
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

#### 3. Task Execution
- **Autonomous Work**: The local LLM:
  1. Parses the task document
  2. Executes steps (e.g., `grep`, `edit`, `view_range`)
  3. Commits changes with `Co-authored-by` trailer
  4. Pushes results to the branch

#### 4. Validation and PR
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

### Example Task Document
See `docs/admin/task-recast-hol-terms.md` for a template.

### Notes
- **Monitoring**: Use `read_agent` to track task progress.
- **Error Handling**: If the task fails, the cloud agent:
  1. Reviews logs via `read_agent`
  2. Updates the task document
  3. Relaunches the task

This procedure ensures tasks are reproducible, auditable, and aligned with SPaDE's distributed development model.