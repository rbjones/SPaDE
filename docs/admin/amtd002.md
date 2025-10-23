# Task Description for Linking Project Documentation to the SPaDE Glossary

## Purpose and Scope

The purpose of this task is to maintain and progress access to the SPaDE project glossary by linking to it appropriately.
The project documentation in the scope of this review consists of all the .md files in the SPaDE project directory and its subdirectories.

## Background

The SPaDE project glossary is contained in [tlad001.md](../tlad001.md).
It is intended to provide definitions and explanations of special terminology and important concepts used in the SPaDE project documentation.
Entries in the glossary are linked to the most appropriate first account of the terminology in the project documentation, either as a document or a section within a document which provides the best available account of its meaning and usage.
There will not always be a suitable link destination, in which case the glossary entry itself must suffice.

## Task Description

Before undertaking this task, familiarise yourself with the contents of the glossary in [tlad001.md](../tlad001.md).
There will already have been a review of the documentation to repair any broken hyperlinks, so repair of broken links is not part of this task, but any encountered should be reported.

The task involves scanning the project documentation for terms which are included in the glossary, and inserting hyperlinks from each occurrence of the term to the corresponding entry in the glossary.
The term itself should be unchanged in the documentation, with only the addition of the hyperlink.
Where a term occurs multiple times in a document, all occurrences should be linked to the glossary entry.

## Deliverables

The resulting edits should be included in a pull request.
A report should be entered into the reviews directory of SPaDE with a name conforming to the document naming conventions specific to reviews in [amms001.md](amms001.md), this should be included in the pull request.
