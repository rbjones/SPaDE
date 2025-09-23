# Remaining Broken Links - Manual Investigation Required

**Date**: September 23, 2025 14:22  
**Contributor**: copilot  
**Status**: 14 broken internal links require manual attention

## Summary

After fixing 9 broken links caused by file renames or incorrect paths, 14 broken links remain that reference non-existent files or directories. These require project maintainer decisions about whether to:
1. Create the missing files/directories
2. Remove the broken links
3. Update the links to reference alternative content

## Detailed Breakdown

### dk/README.md (4 broken links)

**Lines 38-40: Missing Directory Structure**
```markdown
- [Formal Specifications](specs/)
- [API Documentation](docs/)  
- [Metatheory](specs/metatheory.md)
```
**Issue**: dk/ directory lacks specs/ and docs/ subdirectories  
**Recommendation**: Either create these directories with appropriate content or update links to reference existing documentation

**Line 109: Missing Contributing Guidelines**
```markdown
For contribution guidelines, see [CONTRIBUTING.md](../CONTRIBUTING.md).
```
**Issue**: Project lacks CONTRIBUTING.md file at root level  
**Recommendation**: Create CONTRIBUTING.md file or remove reference

### docs/admin/Documentation-Policy.md (2 broken links)

**Line 36: Missing Common Directory**
```markdown
For low-level technical materials common to more than one subsystem, the top-level [common](../../common/) directory will be used.
```
**Issue**: Project lacks common/ directory  
**Recommendation**: Create common/ directory or update documentation policy

**Line 38: Self-Referencing Link**
```markdown
For material of a non-technical nature there is an [admin](admin) subdirectory of the docs directory.
```
**Issue**: Creates circular reference (admin/file linking to admin/)  
**Recommendation**: Remove self-reference or link to parent docs/admin/README.md

### docs/admin/README.md (4 broken links)

**Missing Administrative Documentation Files:**
```markdown
- [**Communication Protocols**](communication-protocols.md)      # Line 21
- [**Review Standards**](review-standards.md)                    # Line 31  
- [**Validation Procedures**](validation-procedures.md)          # Line 32
- [**Feedback Loops**](feedback-loops.md)                       # Line 33
```
**Issue**: Administrative documentation files don't exist  
**Recommendation**: Create these documentation files or remove links from admin README

### kr/README.md (4 broken links)

**Lines 49-50: Missing Review Documentation**
```markdown
- [KR Documentation Review Report](KR_Documentation_Review_Report.md)
- [KR Documentation Action Plan](KR_Documentation_Action_Plan.md)  
```
**Issue**: KR-specific documentation files don't exist  
**Recommendation**: Create these files or reference existing reviews/ directory content

**Line 58: Missing SML File**
```markdown
[m4001.sml](m4001.sml) - Derived SML interface functions
```
**Issue**: m4001.sml file doesn't exist  
**Recommendation**: Generate the SML file or remove reference until available

**Line 72: Missing Contributing Guidelines**
```markdown
For contribution guidelines, see [CONTRIBUTING.md](../CONTRIBUTING.md).
```
**Issue**: Same as dk/README.md - project lacks CONTRIBUTING.md  
**Recommendation**: Create CONTRIBUTING.md file or remove reference

## Priority Recommendations

### High Priority
1. **Create CONTRIBUTING.md** - Referenced by multiple files
2. **Create missing admin documentation** - Core project infrastructure files
3. **Resolve common/ directory question** - Clarify project structure

### Medium Priority  
1. **Create dk/ subdirectories** or update documentation structure
2. **Generate missing KR files** or update references
3. **Fix self-referencing admin link**

### Low Priority
1. **Create m4001.sml** when implementation ready

## Next Steps

Project maintainer should decide on approach for each category of broken links and either:
- Create the missing files/directories with appropriate content
- Update the linking documents to remove broken references  
- Replace broken links with references to existing alternative content

All broken links have been documented with exact file locations and line numbers for easy reference.