# TODO: Glossary Automation Implementation

**Status**: Task descriptions are complete; automation scripts need implementation/enhancement

## Overview

The glossary procedures (amms007.md, amtd002.md, amtd003.md) have been simplified and are ready for copilot execution, but the supporting automation scripts need to be created or enhanced.

## Required Work

### 1. Dynamic Glossary Term Extraction

**New Script**: `docs/admin/extract_glossary_terms.py`

**Purpose**: Parse the glossary file to extract all terms and their anchor links

**Requirements**:
- Parse `docs/tlad001.md` structure
- Extract primary terms from `### Term Name` headers
- Extract variations from `- **Term**:` list items
- Extract variations from `- **[Term](link)**` list items  
- Handle `#### Term` headers if used (per linting guidelines)
- Generate anchor links from term names (lowercase, hyphenated)
- Output JSON format: `{"term": "anchor", ...}`
- Sort by term length (longest first) for compound term handling

**Output Example**:
```json
{
  "Terran Diasporic Repository": "#terran",
  "Terran Diaspora": "#terran",
  "Focal Intelligence": "#focal",
  "Focal AI": "#focal",
  "SPaDE": "#spade",
  ...
}
```

### 2. Enhanced Glossary Linking Script

**Modify**: `docs/admin/amcd001.py`

**Current State**: Works for full reviews with hard-coded terms

**Required Enhancements**:

#### 2.1 Dynamic Term Loading
- Replace hard-coded TERMS list
- Read terms from `extract_glossary_terms.py` output
- Add `--terms-file` parameter (default: auto-extract from glossary)

#### 2.2 Incremental Mode Support
- Add `--since-date YYYY-MM-DD-HHMM` parameter
- Use git to identify files modified since date
- Add `--new-terms-only` flag for unchanged files
- Add `--changed-files` parameter to process specific file list

#### 2.3 File Filtering
- Add `--files` parameter to accept specific file list
- Split processing: changed files (all terms) vs unchanged files (new terms only)

#### 2.4 Report Generation
- Add `--report` parameter for output filename
- Generate markdown report with:
  - Last review date (from parameter)
  - Files processed (count changed vs unchanged)
  - New terms checked (list)
  - Links added per file
  - Total statistics
  - Any issues encountered
- Default report filename: `reviews/YYYYMMDD-HHMM-copilot-glossary-links.md`

#### 2.5 Testing
- Test with dry-run on incremental changes
- Verify compound term handling
- Verify code block/link/heading avoidance still works

### 3. Candidate Term Discovery

**New Script**: `docs/admin/find_candidate_terms.py`

**Purpose**: Identify potential terms for glossary augmentation

**Requirements**:
- Scan all markdown files (excluding reviews/, retro/, .*)
- Extract potential technical terms using patterns:
  - Capitalized phrases (2-4 words)
  - Technical compounds
  - Domain-specific terminology
- Filter out existing glossary terms
- Count frequency across files
- Rank by importance (frequency, location in headings, etc.)
- Output candidate list with:
  - Term
  - Frequency count
  - Files where it appears
  - Example contexts (snippets)

**Output Example**:
```markdown
## Candidate Glossary Terms

### High Priority (5+ occurrences)

#### Pansophic Repository
- Occurrences: 8
- Files: docs/architecture.md, docs/design.md, README.md
- Context: "...the pansophic repository serves as..."

#### Deductive Kernel
- Occurrences: 12
- Files: dk/README.md, docs/architecture.md
- Context: "...implemented in the deductive kernel..."
```

### 4. Integration Testing

Before declaring ready for test run:

1. **Test extract_glossary_terms.py**:
   - Run on current glossary
   - Verify all terms extracted correctly
   - Check anchor generation matches actual glossary anchors

2. **Test enhanced amcd001.py**:
   - Dry-run with dynamic term extraction
   - Test incremental mode with mock date
   - Verify report generation
   - Compare output with previous manual run

3. **Test find_candidate_terms.py**:
   - Run on current documentation
   - Review candidate quality
   - Verify filtering works correctly

4. **End-to-end test**:
   - Add a new test term to glossary
   - Run incremental glossary linking (amtd002.md)
   - Verify only new term gets linked
   - Verify report is generated correctly

## Implementation Priority

### Phase 1 (Required for glossary linking test run)
1. `extract_glossary_terms.py` - Critical
2. Enhanced `amcd001.py` with dynamic loading - Critical
3. Enhanced `amcd001.py` with incremental mode - Critical
4. Enhanced `amcd001.py` with reporting - Critical

### Phase 2 (Required for glossary augmentation test run)
5. `find_candidate_terms.py` - Important
6. Integration testing - Important

## Estimated Complexity

- **extract_glossary_terms.py**: ~100 lines, moderate (regex parsing, JSON output)
- **amcd001.py enhancements**: ~150 lines added, moderate (git integration, report generation)
- **find_candidate_terms.py**: ~200 lines, moderate (NLP-lite term extraction)
- **Testing**: ~2-3 hours, straightforward

## Notes

- All scripts should follow existing code style in amcd001.py
- Add comprehensive help text for command-line usage
- Include error handling for missing files, invalid dates, etc.
- Consider using `argparse` for consistent CLI interface
- Document any external dependencies (should be minimal - standard library preferred)
