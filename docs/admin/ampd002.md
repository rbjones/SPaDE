# Process for completing code and test assignments

## Status

Historical context document.

For current baseline practice, use:

1. [ampd004.md](ampd004.md) for branches, worktrees, and session scope
2. [ampd005.md](ampd005.md) for independent review (Grok authors, Copilot reviews)
3. [ampd008.md](ampd008.md) for issue-backed Copilot delegation and task templates

When you are assigned a code or test task, please follow these steps to ensure a smooth and efficient completion:

1. **Create a new branch** from the main branch of the repository.

2. **Understand the Requirements**: Carefully read the assignment details to fully understand what is expected.
  If anything is unclear, reach out to the assigner for clarification. These should include detailed design documents, and description of the module test method.
  In creating documents for the assignment, please follow the documentation standards outlined in [Project Structure and Documentation Policy amms001.md](amms001.md).
  
  The task description should include:

    - The subsystem to which the code or test belongs. (top level sub-directory)
    - The filenames for the specifications, including the module test design document.
    - The filenames for the code or test files to be created or modified.
    - The filenames for the makefile for the module tests.

    If there are any problems with the requirements, the first draft pull request should include a review document that outlines the issues (see document standards for review documents naming and placement)

3. **Edit Makefile to incorporate module tests** This will usually be the makefile for one of the major subsystems.
