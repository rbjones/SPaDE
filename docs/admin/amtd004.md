# Task Description for Implementation of Glossary Automation Scripts

## Purpose and Scope

The purpose of this task is to implement the automation scripts required to support the incremental glossary procedures defined in [amtd002.md](amtd002.md) (glossary linking) and [amtd003.md](amtd003.md) (glossary augmentation).

The scope includes creating new scripts and enhancing existing scripts in the `docs/admin/` directory to enable automated, incremental glossary maintenance.

## Background

The glossary procedures have been defined and documented:
- [amms007.md](amms007.md) - Method for glossary augmentation
- [amtd002.md](amtd002.md) - Task description for incremental glossary linking
- [amtd003.md](amtd003.md) - Task description for glossary augmentation

These procedures require automation support that does not yet exist or needs enhancement in the current tooling.

## Required Scripts

### 1. Create: `extract_glossary_terms.py`

**Purpose**: Parse the glossary file to dynamically extract all terms and their anchor links.

**Requirements** (per [amtd002.md](amtd002.md)):
- Parse `docs/tlad001.md` structure
- Extract primary terms from `### Term Name` headers
- Extract variations from `- **Term**:` list items and `- **[Term](...)**` patterns
- Extract `#### Term` headers if used (per linting guidelines)
- Generate appropriate anchor links
- Output in a format consumable by the linking script
- Sort by term length (longest first) for compound term handling

### 2. Enhance: `amcd001.py`

**Purpose**: Extend existing glossary linking script to support incremental operation.

**Current State**: Works for full reviews with hard-coded term list.

**Required Enhancements** (per [amtd002.md](amtd002.md)):
- Replace hard-coded TERMS list with dynamic term loading from `extract_glossary_terms.py`
- Add command-line parameter to process only files modified since a specified date (using git)
- Add mode to check only new terms in unchanged files
- Generate review report in markdown format per specification in [amtd002.md](amtd002.md)
- Support file filtering to process specific file lists

### 3. Create: `find_candidate_terms.py`

**Purpose**: Identify potential terms for glossary augmentation.

**Requirements** (per [amtd003.md](amtd003.md) and [amms007.md](amms007.md)):
- Scan documentation for technical terminology not in the glossary
- Filter by frequency and importance
- Output candidate list with usage contexts
- Support the term discovery process described in [amms007.md](amms007.md)

## Deliverables

1. **New script**: `docs/admin/extract_glossary_terms.py`
2. **Enhanced script**: `docs/admin/amcd001.py` with incremental capabilities
3. **New script**: `docs/admin/find_candidate_terms.py`
4. **Testing**: Verification that scripts work correctly with the procedures in [amtd002.md](amtd002.md) and [amtd003.md](amtd003.md)

## Success Criteria

Scripts are complete when:
- A test run of the glossary linking task ([amtd002.md](amtd002.md)) can be successfully executed by copilot
- A test run of the glossary augmentation task ([amtd003.md](amtd003.md)) can be successfully executed by copilot
- All scripts follow project coding standards and include appropriate documentation
