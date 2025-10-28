# Incremental Glossary Linking Procedure Analysis and Proposal

**Date**: October 28, 2025 14:30  
**Reviewer**: GitHub Copilot  
**Subject**: Proposal for efficient incremental glossary linking procedures

## Analysis of Current Situation

### Previous Review Context

The last comprehensive glossary linking review was completed on **2025-10-23** ([20251023-1356-copilot-glossary-links.md](20251023-1356-copilot-glossary-links.md)), which:

- Processed **45 markdown files**
- Added **354 glossary links**
- Used a hard-coded list of **20 glossary terms**
- Established baseline coverage across all documentation

### Current Glossary State

Analysis of `docs/tlad001.md` reveals the current glossary contains:

**Primary Terms** (### headers):

- Declarative Knowledge
- Deduction
- Deductive Engineering
- Diasporic
- Epistemology
- Epistemological Stack
- Focal
- Pansophic
- The Singularity
- Singular Focus
- SPaDE
- Synthetic
- Terran

**Term Variations** (bold phrases):

- Diasporic Repository
- Focal Intelligence, Focal AI, Focal Engineering, Focal Tower
- Synthetic Epistemology, Synthetic Philosophy
- Terran Diaspora, Terran Diasporic Repository

## Identified Issues with Current Approach

### 1. Hard-Coded Term Management

- Script contains static TERMS list requiring manual maintenance
- Risk of missing new glossary additions
- No validation that script terms match actual glossary content

### 2. Inefficient Full Scans

- Every review processes all files regardless of changes
- No differentiation between new terms vs new content
- Scales poorly as project grows

### 3. Limited Change Detection

- No mechanism to identify files modified since last review
- No tracking of glossary evolution between reviews
- Manual comparison required to detect scope changes

## Proposed Incremental Procedure

### Phase 1: Change Analysis

#### 1.1 Glossary Change Detection

```bash
# Extract current glossary terms
python3 extract_glossary_terms.py docs/tlad001.md > current_terms.json

# Compare with previous review
diff previous_review_terms.json current_terms.json
```

#### 1.2 File Change Detection  

```bash
# Find files modified since last glossary review (2025-10-23 13:56)
git log --since="2025-10-23 13:56" --name-only --pretty=format: \
    | grep '\.md$' | grep -v '^reviews/' | grep -v '^retro/' | sort -u
```

### Phase 2: Scoped Processing

#### 2.1 Changed Files (Full Term Check)

- Process all files modified since last review
- Check for ALL glossary terms (existing + new)
- Rationale: Changed content may introduce contexts for any term

#### 2.2 Unchanged Files (New Terms Only)

- Process all unchanged files  
- Check ONLY for terms added since last review
- Rationale: Existing terms already processed in previous review

#### 2.3 New Files (Full Term Check)

- Process any files created since last review
- Check for ALL glossary terms
- Rationale: New files need complete glossary coverage

### Phase 3: Enhanced Script Requirements

#### 3.1 Dynamic Glossary Parsing

```python
def extract_glossary_terms(glossary_file):
    """Extract all terms and variations from glossary markdown."""
    # Parse ### headers as primary terms
    # Extract **bold** phrases as variations  
    # Build term -> anchor mapping
    # Return comprehensive term list
```

#### 3.2 Incremental Mode Support

```python
def incremental_scan(file_list, term_list, mode='full'):
    """Support targeted scanning modes."""
    # mode='full': check all terms in file_list
    # mode='new_terms': check only new_terms in file_list
    # Generate differential reports
```

#### 3.3 Change Tracking

```python
def generate_change_report(previous_report, current_scan):
    """Compare review states and report changes."""
    # Files added/modified/deleted
    # Terms added/removed/modified
    # Link coverage changes
```

## Implementation Recommendations

### Priority 1: Glossary Term Extraction

Create `extract_glossary_terms.py` to dynamically parse glossary content and eliminate hard-coded term lists.

### Priority 2: Enhanced Main Script

Modify `amcd001.py` to support:

- Dynamic term loading
- File filtering by modification date
- Incremental vs full mode operation
- Detailed change reporting

### Priority 3: Review Workflow

Update `amtd002.md` task description to specify:

- When to use incremental vs full review
- How to determine file and term scope
- Required deliverables for each review type

## Efficiency Analysis

### Current Full Review

- **Time Complexity**: O(F × T) where F=files, T=terms
- **Last Review**: 45 files × 20 terms = 900 file-term combinations

### Proposed Incremental Review (Typical)

Assuming 10% files changed, 2 new terms:

- **Changed files**: 5 files × 22 terms = 110 combinations  
- **Unchanged files**: 40 files × 2 terms = 80 combinations
- **Total**: 190 combinations (78% reduction)

## Risk Mitigation

### 1. Accuracy Preservation

- Periodic full reviews (quarterly) to validate incremental accuracy
- Cross-validation of git change detection
- Manual spot-checks of high-impact files

### 2. Edge Case Handling

- Handle glossary reorganization (term moves/renames)
- Detect and report potential missed terms
- Validate relative path changes

### 3. Quality Assurance

- Automated link validation in generated content
- Regression testing against known good states
- Human review of automated changes

## Conclusion

The proposed incremental procedure addresses efficiency concerns while maintaining comprehensive coverage. The key innovations are:

1. **Dynamic glossary parsing** eliminates maintenance overhead
2. **Change-based scoping** reduces processing by ~80% in typical cases  
3. **Differential reporting** provides clear visibility into review scope and changes

This approach scales effectively with project growth while ensuring no terms or files are overlooked in the linking process.
