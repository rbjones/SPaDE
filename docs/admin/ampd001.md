# Using GitHub Copilot Agent with SPaDE

**Document ID**: ampd001.md  
**Category**: Process or procedure descriptions  
**Subsystem**: docs/admin (am)

## Overview

This document describes how to assign autonomous code-and-test tasks to GitHub Copilot agents, enabling them to create PRs that are automatically tested in the SPaDE development container.

## Workflow

1. Create an issue describing the task
2. Use GitHub Copilot Workspace or comment `@copilot implement this`
3. Copilot creates a branch and implements changes
4. Copilot opens a PR
5. GitHub Actions tests the changes in the SPaDE container
6. Review and merge if tests pass, otherwise diagnose, fix and go to 5.

## Key Distinction: Two Modes of Copilot Usage

**Interactive Mode (Current)**: Working directly in this dev container via chat - Copilot has direct access to run commands, test iteratively, and see immediate results.

**Autonomous Agent Mode (This Document)**: Copilot works at arm's length - generates code, opens PR, CI tests run, Copilot reviews logs, iterates if needed. No interactive container access.

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

You'll need a GitHub Personal Access Token with `write:packages` scope from https://github.com/settings/tokens

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

Autonomous agents work at arm's length - they cannot interactively debug ProofPower sessions. For complex ProofPower integration tasks, interactive mode (working in this dev container) may be more effective.
