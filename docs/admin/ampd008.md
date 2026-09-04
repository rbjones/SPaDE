# Copilot Delegation Procedure with Task Documents

**Document ID**: ampd008.md  
**Category**: Process or procedure descriptions  
**Subsystem**: docs/admin (am)

## Purpose

Define a repeatable procedure for assigning implementation tasks to Copilot coding agent while preserving full traceability.

This is the GitHub-scheduled Copilot path ([README.md](README.md) working practice, [ampd001.md](ampd001.md)). Copilot creates its own branch; it does not check out an area worktree. Area worktrees are for Grok ([ampd004.md](ampd004.md)).

## Policy

For non-trivial tasks, use all three artefacts:

1. A task description document in `docs/admin/` using the `amtd*.md` series
2. A GitHub issue which links that task description
3. A Copilot coding-agent request which references the issue and task description

For tiny mechanical edits, the issue may be omitted, but the pull request body must still contain a complete task record.

## Branching and PR Target Rules

1. The intended base branch must exist on the remote repository.
2. Copilot assignment must explicitly set the base branch parameter (for example `base_ref`).
3. The prompt text must repeat the same branch target to avoid ambiguity.
4. If parameter and prompt disagree, treat the explicit parameter as authoritative.
5. Pull request base must be checked before review begins.

## Standard Procedure

1. Prepare or update the task description document (`amtd*.md`).
2. Open an issue that links the task document and states the required base branch.
3. Delegate to Copilot coding agent with explicit `base_ref`.
4. Require the resulting PR body to include the task record sections listed below.
5. Request Copilot review and human review.
6. Merge only when acceptance criteria and evidence from the task document are satisfied.

## Required Task Record in PR Body

Every Copilot-authored PR for this workflow must include:

1. Objective
2. Source task document and issue links
3. Scope and out-of-scope
4. Acceptance criteria
5. Assumptions and risks
6. Test evidence (commands and outcomes)
7. Files changed with rationale
8. Follow-up tasks

## Template: Task Description (`amtd*.md`)

Use this as a starting pattern for each new task description file.

```markdown
# Task Description for <short task title>

## Purpose and Scope

<what this task is for, and what is in scope>

## Background

<context, prior documents, constraints, assumptions>

## Branch and Integration Target

- Working branch (base_ref): `<branch-name>`
- Pull request base branch: `<branch-name>`
- Tests: SPaDE container (Copilot has no local workspace)

## Task Requirements

1. <requirement>
2. <requirement>
3. <requirement>

## Out of Scope

- <explicit exclusions>

## Deliverables

1. <files or artefacts to be created/updated>
2. <tests or reports>
3. <documentation updates>

## Acceptance Criteria

1. <observable pass condition>
2. <observable pass condition>
3. <observable pass condition>

## Validation

- Commands to run:
  - `<command>`
  - `<command>`
- Expected outcomes:
  - <expected result>
  - <expected result>

## References

- <doc link>
- <doc link>
```

## Template: Issue Body

Use this issue template when delegating to Copilot.

```markdown
## Summary

<one paragraph summary>

## Authoritative Task Description

- <link to amtd document>

## Branching

- base_ref: `<branch-name>`
- PR base: `<branch-name>`

## Acceptance Criteria

1. <criterion>
2. <criterion>
3. <criterion>

## Required PR Content

The PR must include: objective, scope/out-of-scope, assumptions, risks, tests run, outcomes, files changed with rationale, and follow-up tasks.
```

## Template: Copilot Coding-Agent Request

Use this in Copilot Chat (or equivalent delegation surface).

```text
Create a Copilot coding-agent task for repo <owner>/<repo>.

Title: <short title>
Base branch (base_ref): <branch-name>

Implement strictly according to:
- Issue: <issue-link>
- Task description: <amtd-link>

Create a PR targeting <branch-name> and include a Task Record section with:
1) Objective
2) Scope and Out of Scope
3) Acceptance Criteria status
4) Assumptions and Risks
5) Tests run and outcomes
6) Files changed and rationale
7) Follow-up tasks
```

## Notes

- This procedure does not require creating new document-type families.
- Templates are maintained here as part of procedure documentation.
- Task-specific detail belongs in `amtd*.md` files, not only in issue or chat text.
