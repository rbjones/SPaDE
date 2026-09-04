# Using GitHub Copilot Agent with SPaDE

**Document ID**: ampd001.md  
**Category**: Process or procedure descriptions  
**Subsystem**: docs/admin (am)

## Status

Current procedure for **GitHub-scheduled** Copilot work (issues, coding agent, PRs). Interactive discussion and local editing are Grok Build ([README.md](README.md) working practice, [ampd004.md](ampd004.md)). Independent review of *Grok-authored* PRs is [ampd005.md](ampd005.md). Task templates: [ampd008.md](ampd008.md).

Copilot’s model is often selectable and is not assumed to be Grok.

## Overview

This document describes how to assign autonomous code-and-test tasks to GitHub Copilot agents. Copilot has no access to the local workspace, so tests must run in the SPaDE development container.

## Workflow

1. Create an issue describing the task
2. Use GitHub Copilot Workspace or comment `@copilot implement this`
3. Copilot creates a branch and implements changes
4. Copilot opens a PR
5. GitHub Actions tests the changes in the SPaDE container
6. Review and merge if tests pass, otherwise diagnose, fix and go to 5.

## Scope of this document

This is **autonomous / GitHub** Copilot only: generate code, open a PR, CI tests in the SPaDE container, iterate from logs. It is not interactive Copilot Chat in a local or codespace tree. Interactive work is Grok Build.

When Copilot authors the PR, Copilot is not the independent reviewer of that PR ([ampd005.md](ampd005.md)).

## Container Strategy

To avoid rebuilding the ProofPower environment on every test iteration, SPaDE uses a pre-built container:

**Base**: `ghcr.io/rbjones/pp/proofpower:latest` (ProofPower installation)  
**SPaDE Container**: `ghcr.io/rbjones/spade:latest` (adds Python, dependencies, SPaDE code)

This matches the pattern used in `rbjones/pp` repository's `build-container.yml` workflow.

## Configured Components

### 1. Workflows

**`.github/workflows/copilot-agent-test.yml`**: Runs on all PRs, uses SPaDE container, executes tests

**`.github/workflows/build-spade-container.yml`**: Builds SPaDE container from ProofPower base, manually triggered

**`.github/workflows/test-spade-integration.yml`**: Manual comprehensive testing

### 2. Helper Script

**`common/push-container.sh`**: Pushes locally-saved container to GHCR

## Initial Setup

### Push Your Saved Container

From your **host machine**:

```bash
cd /path/to/SPaDE/common
./push-container.sh
```

You'll need a GitHub Personal Access Token with `write:packages` scope from <https://github.com/settings/tokens>

### Alternative: Build via GitHub Actions

Instead of pushing locally-saved container, trigger "Build SPaDE Container" workflow in GitHub Actions (takes longer, but only needs doing once).

## Creating Issues for Autonomous Completion

Structure issues with: Task description, Context (files, ProofPower theories), Requirements, Testing approach, Definition of Done.

**Example**: "Create Python script `kr/krcd007.py` to extract HOL theory hierarchy from ProofPower via subprocess, output to `kr/krcd004.json`, include pytest tests."

## Using the Agent

- **GitHub Web**: Use Copilot Workspace to reference an issue
- **Issue Comments**: Comment `@copilot implement this`
- **VS Code**: Use `#github-pull-request_copilot-coding-agent` in Copilot Chat

## Monitoring

- Check Pull Requests for Copilot-created PRs
- Review "Checks" tab for test results
- Locally test via `gh pr checkout <PR-number>`

## Current Limitations

Autonomous agents work at arm's length: they cannot interactively debug ProofPower sessions. For that class of work, specify and explore in Grok Build, then hand a bounded task to Copilot via an issue, or run tests in the SPaDE container yourself.
