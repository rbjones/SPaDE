# Task Description for Review of Hyperlinks in Project Documentation

## Purpose and Scope

The purpose is to ensure integrity and completeness of the presentation of project documentation through github pages.
The Scope will either be the entire [SPaDE](../tlad001.md#spade) repository (the default) or specified subdirectories, but is restricted to the documentation files in markdown format (.md) only. Historical material in the `reviews/` directory, all content under `retro/`, and any directory whose name begins with `.` are excluded from this task, except that any new report produced as part of the deliverables must still be placed in `reviews/`.

## Background

The documentation policy for the [SPaDE](../tlad001.md#spade) project is in [amms001.md](amms001.md).
The project root and each directory has a README.md file which provides an overview of the contents of that directory and links to the documents within it. All .md files in the directory should be linked from the README.md file for that directory or a subdirectory.
In addition, documents may cross refer to other documents in the project.

## Task Description

This task can be performed either as a full review or as an incremental review:

- **Full review**: Check all files in scope
- **Incremental review**: Focus on files modified since last review

**Important**: Even in incremental reviews, when checking for broken links, ALL files must be scanned because:

- An unchanged link in file A may now be broken if file B was renamed or deleted
- File renames and deletions affect link validity across the entire repository

The incremental aspect applies to determining which files may have introduced new links or changed existing ones, but broken link detection requires checking all files for validity of their link targets.

### Completeness Check

First check recursively that all .md files in the specified scope and its subdirectories are linked from the README.md file for their directory.
Missing links should be included in a new version of the README.md file for that directory.
Links should be included in the README.md file in a style and structure similar to the existing links in the file.

### Hyperlink Validation

Once completeness of the README.md files has been ensured, check all hyperlinks in all .md files in the specified scope.
For each hyperlink, check that it points to an existing file in the project, and that if it points to a specific section within that file, that the section exists.
For external links (e.g., to GitHub or other sites), verify that they are still valid and accessible; update or remove if broken.
For any broken links, either repair the link if the target section or file has been moved, or remove the link if the target section or file has been deleted.

While undertaking these transformations a report should be compiled in which any unresolved issues are highlighted, and any corrections are noted.

## Deliverables

The resulting edits and the report should be included in a pull request. The report should be entered into the reviews directory of [SPaDE](../tlad001.md#spade) with a filename following the pattern `YYYYMMDD-HHMM-author-topic.md` (e.g., `20250101-1430-copilot-link-review.md`). Reference any specific GitHub workflow for submission if applicable.
