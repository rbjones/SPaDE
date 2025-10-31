# Task Description for Incremental Glossary Linking

## Purpose and Scope

The purpose of this task is to maintain access to the [SPaDE](../tlad001.md#spade) project glossary by incrementally adding links from documentation to glossary entries as changes occur.
The project documentation in scope consists of all .md files in the [SPaDE](../tlad001.md#spade) project directory and its subdirectories, excluding the `reviews/` and `retro/` directories and any directory whose name begins with `.`.

## Background

The [SPaDE](../tlad001.md#spade) project glossary is contained in [tlad001.md](../tlad001.md).
Entries in the glossary define special terminology and important concepts used in the project documentation.

## Task Description

This task performs **incremental glossary linking** - adding links for terms that have been recently added to the glossary or appear in recently modified documentation.

### Determining Review Scope

1. **Identify last review date**: Check the reviews directory for the most recent glossary linking review report (filename pattern `YYYYMMDD-HHMM-*-glossary-links.md`)
2. **Extract terms from glossary**: Dynamically scan [tlad001.md](../tlad001.md) to get current term list
3. **Determine what changed**:
   - Files modified since last review date (using git)
   - New glossary terms added since last review
   - New files created since last review

### Processing Strategy

#### Changed or New Files
Process files modified or created since the last review, checking for ALL glossary terms (both existing and newly added).

#### Unchanged Files  
Process all unchanged files, but check ONLY for newly added glossary terms.

**Note**: Although files are unchanged, they must all be checked when new terms are added to catch occurrences of those new terms throughout the documentation.

### Glossary Term Extraction

Automatically extract all terms from the glossary by:

- Parsing section headers (### level) as primary terms
- Extracting variations from list items starting with `- **Term**:` 
- Building a comprehensive term list with anchor links
- Noting compound terms to ensure longer phrases are processed before shorter ones

### Linking Rules

Insert hyperlinks from term occurrences to the corresponding glossary entry, following these rules:

- Term text remains unchanged, only add the hyperlink
- Link all occurrences of a term within a document
- For compound terms, link the longest matching phrase (e.g., "Focal Intelligence" not "Focal" within that phrase)
- Skip terms in contexts where the meaning differs from the glossary definition

Avoid linking terms that are:
- Already inside existing markdown links
- Inside code blocks (inline or fenced)
- In headings (to preserve heading structure)
- In URLs or other special contexts

## Automation Support

A Python script is available at `docs/admin/amcd001.py` to assist with this task.

**Required enhancements for incremental operation**:

1. **Dynamic term extraction**: Parse glossary file to extract all terms automatically
2. **File filtering**: Accept list of files to process based on git change detection
3. **Term filtering**: Accept list of new terms to check in unchanged files
4. **Reporting**: Generate comparison report showing links added vs previous review

The script should process longer phrases before shorter ones to handle compound terms correctly, and avoid linking terms in code blocks, existing links, and headings.

## Deliverables

1. **Updated documentation files** with new glossary links added
2. **Review report** in the reviews directory with filename `YYYYMMDD-HHMM-author-glossary-links.md` containing:
   - Last review date used for change detection
   - Number of files processed (changed vs unchanged)
   - Number of new terms checked
   - Total links added
   - Any issues or edge cases encountered

Include both the file changes and report in a pull request.
