# Task Description for Linking Project Documentation to the SPaDE Glossary

## Purpose and Scope

The purpose of this task is to maintain and progress access to the [SPaDE](../tlad001.md#spade) project glossary by linking to it appropriately.
The project documentation in the scope of this review consists of all the .md files in the [SPaDE](../tlad001.md#spade) project directory and its subdirectories, excluding the `reviews/` and `retro/` directories and any directory whose name begins with `.`.

## Background

The [SPaDE](../tlad001.md#spade) project glossary is contained in [tlad001.md](../tlad001.md).
It is intended to provide definitions and explanations of special terminology and important concepts used in the [SPaDE](../tlad001.md#spade) project documentation.
Entries in the glossary are linked to the most appropriate first account of the terminology in the project documentation, either as a document or a section within a document which provides the best available account of its meaning and usage.
There will not always be a suitable link destination, in which case the glossary entry itself must suffice.

## Task Description

This task supports both **initial comprehensive reviews** and **incremental reviews** for glossary linking.

### Preparation Phase

1. **Scan the glossary** in [tlad001.md](../tlad001.md) to extract all defined terms and their variations
2. **Identify scope** for this review:
   - **Full review**: Process all eligible markdown files
   - **Incremental review**: Process only files modified since the last glossary linking review, plus check all files for any new glossary terms added since the last review

### Glossary Term Extraction

Before processing files, automatically extract all terms from the glossary by:

- Parsing section headers (### level) as primary terms
- Extracting bold phrases (**text**) as term variations  
- Building a comprehensive term list with anchor links
- Noting compound terms (e.g., "Terran Diasporic Repository" vs "Terran")

### Core Task

The task involves scanning the project documentation for terms which are included in the glossary, and inserting hyperlinks from each occurrence of such terms to the corresponding entry in the glossary.
The term itself should be unchanged in the documentation, with only the addition of the hyperlink.
Where a term occurs multiple times in a document, all occurrences should be linked to the glossary entry.

The review should cover all markdown (.md) files in the SPaDE project directory and subdirectories, excluding:

- The `reviews/` directory
- The `retro/` directory  
- Any directory whose name begins with `.`
- The glossary file itself (docs/tlad001.md) and any other files which might later be created to document the glossary.

The following special cases should be noted:

- If a term is used in a context where it has a different meaning from that given in the glossary, do not insert a hyperlink.
- If a term is part of a compound term (e.g., "Focal Intelligence"), only link the part of the term which is in the glossary (e.g., "Focal").
If both a part and a whole are in the glossary, link only the whole (e.g., link "Focal Intelligence" but not "Focal" in that phrase).

- Avoid linking terms that are:
  - Already inside existing markdown links
  - Inside code blocks (inline or fenced)
  - In headings (to preserve heading structure)
  - In URLs or other special contexts

## Incremental Review Procedure

For efficient incremental reviews, determine:

1. **Files changed since last review**: Use git to identify files modified since the timestamp of the last glossary review report
2. **New glossary terms**: Compare current glossary content with the term list from the previous review report to identify newly added terms
3. **Processing strategy**:
   - **Changed files**: Check for ALL glossary terms (existing + new)  
   - **Unchanged files**: Check only for NEW glossary terms
   - **New files**: Check for ALL glossary terms

This approach ensures comprehensive coverage while minimizing unnecessary work.

## Automation Support

There is a python script available to assist with this task, which can be found at `docs/admin/amcd001.py` in the SPaDE project repository.

**Current limitations**: The script uses a hard-coded term list and should be enhanced to:

1. **Dynamically extract** terms from the glossary file
2. **Support incremental mode** by accepting file lists and term lists as parameters
3. **Generate reports** comparing current vs previous glossary coverage

The script processes longer phrases first to handle compound terms correctly, and avoids linking terms in code blocks, existing links, and headings.

## Deliverables

The resulting edits should be included in a pull request.
A report should be entered into the reviews directory of [SPaDE](../tlad001.md#spade) with a filename following the pattern `YYYYMMDD-HHMM-author-topic.md` (e.g., `20250101-1430-copilot-glossary-links.md`), this should be included in the pull request.
