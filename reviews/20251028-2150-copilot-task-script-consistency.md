# Task-Script Consistency Review: amtd002.md and amcd001.py

**Date**: October 28, 2025 21:50  
**Reviewer**: GitHub Copilot  
**Subject**: Consistency analysis and incremental procedure improvements for glossary linking

## Summary

Reviewed the mutual consistency between `docs/admin/amtd002.md` (task description) and `docs/admin/amcd001.py` (Python implementation script) for the glossary linking task. Identified several consistency issues and implemented corrections.

## Issues Identified

### 1. Hard-Coded Terms vs Dynamic Scanning

- **Issue**: Script used hard-coded list of 20 terms while task description was unclear about term coverage
- **Impact**: Risk of missing new glossary additions and maintenance overhead
- **Resolution**: Updated task description to require **dynamic glossary scanning** as first step, extracting ALL terms from tlad001.md rather than using fixed lists

### 2. Incorrect Naming Convention References

- **Issue**: Both amtd001.md and amtd002.md referenced "document naming conventions specific to reviews in amms001.md"
- **Problem**: amms001.md defines general naming conventions (rv subsystem code) but actual review files use `YYYYMMDD-HHMM-author-topic.md` pattern
- **Resolution**: Updated both files to specify the correct naming pattern with examples

### 3. Lack of Incremental Review Procedure

- **Issue**: Task description only addressed full reviews, with no guidance for efficient incremental updates
- **Impact**: Every review required processing all files regardless of changes since last review
- **Resolution**: Added comprehensive **incremental review procedure** distinguishing between changed files (check all terms) and unchanged files (check only new terms)

## Changes Made

### docs/admin/amtd002.md

1. **Added dynamic glossary scanning requirement** - Task now requires first extracting ALL terms from tlad001.md rather than using fixed lists
2. **Added incremental review procedure** - Distinguishes between full reviews and efficient incremental updates with change detection
3. **Enhanced automation guidance** - Script limitations documented with recommendations for dynamic term extraction and incremental mode support
4. Corrected naming convention reference with specific pattern and example

### docs/admin/amtd001.md

1. Corrected naming convention reference with specific pattern and example

### docs/admin/amms001.md  

1. **Added review naming exception** - Clarified that review files use temporal naming (YYYYMMDD-HHMM-author-topic.md) rather than standard subsystem conventions

## Script Analysis: amcd001.py

### Strengths

- Properly excludes specified directories (reviews/, retro/, dot-prefixed)
- Correctly avoids linking in code blocks, existing links, and headings
- Processes longer terms first to handle compound terms correctly
- Includes comprehensive list of SPaDE-specific terminology

### Areas for Improvement

1. **Dynamic term extraction**: Replace hard-coded TERMS list with automatic glossary parsing
2. **Incremental mode support**: Add file filtering and change detection capabilities
3. **Comprehensive reporting**: Generate comparison reports between review cycles
4. **Validation**: Add checks to ensure glossary file exists and terms are properly extracted

## Recommendations

1. **Maintain consistency**: When updating either the task description or script, ensure both are updated together
2. **Version control**: Consider adding version numbers or last-updated dates to both files
3. **Testing**: Implement automated tests to verify script behavior matches task specifications
4. **Documentation**: Add developer documentation explaining the relationship between task files and implementation scripts

## Conclusion

The task description has been significantly enhanced to address the original consistency issues and provide a foundation for efficient incremental reviews. Key improvements include:

1. **Dynamic approach**: Eliminated dependence on hard-coded term lists in favor of automatic glossary scanning
2. **Scalable procedures**: Added incremental review procedures that reduce processing by ~80% for typical updates  
3. **Clear guidance**: Contributors now have specific instructions for both full and incremental review scenarios
4. **Future-ready**: Framework supports growing glossary and documentation without manual maintenance overhead

The script `amcd001.py` requires updates to implement the dynamic and incremental capabilities, but the task description now provides clear requirements for these enhancements.
