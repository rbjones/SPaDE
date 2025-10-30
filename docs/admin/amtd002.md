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

Before undertaking this task, familiarise yourself with the contents of the glossary in [tlad001.md](../tlad001.md).
There will already have been a review of the documentation to repair any broken hyperlinks, so repair of broken links is not part of this task, but any encountered should be reported.

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

There is a python script available to assist with this task, which can be found in the `docs/admin/amcd001.py` of the SPaDE project repository.
This script should be reviewed against these instructions and if necessary modifications to it and or this task description to reconciliate the two should be proposed.

## Deliverables

The resulting edits should be included in a pull request.
A report should be entered into the reviews directory of [SPaDE](../tlad001.md#spade) with a name conforming to the document naming conventions specific to reviews in [amms001.md](amms001.md), this should be included in the pull request.
