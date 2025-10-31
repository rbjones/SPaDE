# Glossary Augmentation Procedure

## Purpose

This document describes the method for systematically identifying new technical terms in the SPaDE project documentation that should be added to the glossary.

## Scope

This procedure applies to all markdown (.md) files in the SPaDE repository, excluding:

- The `reviews/` directory
- The `retro/` directory  
- Any directory whose name begins with `.`
- The glossary file itself (`docs/tlad001.md`)

## Procedure Overview

### Step 1: Link Identification

For each candidate term, first check if there is a suitable detailed account of the term's meaning elsewhere in the project documentation:

1. **Search documentation** for sections that explain the term in detail
2. **Assess suitability** - Is the explanation comprehensive and stable?
3. **If suitable account exists**: Note the document/section for linking from the glossary entry
4. **If no suitable account exists**: The glossary entry will need to provide the full definition

This ensures glossary entries link to authoritative explanations where available, with the glossary providing contracted or standalone definitions as needed.

### Step 2: Term Discovery

#### Automated Scanning

1. **Scan eligible markdown files** for potential technical terms
2. **Extract candidates** using linguistic patterns:
   - Capitalized phrases (2-4 words)
   - Technical compounds (e.g., "knowledge repository", "deductive kernel")  
   - Domain-specific terminology (AI, logic, philosophy terms)
   - Project-specific concepts and methodologies

#### Filtering

1. **Exclude existing glossary terms** by comparing against current `docs/tlad001.md`
2. **Filter by frequency** - terms appearing in multiple contexts
3. **Prioritize by importance**:
   - Usage frequency across files
   - Centrality to project architecture
   - Technical complexity requiring definition
   - Potential for confusion or ambiguity

### Step 3: Term Analysis

For each candidate term:

1. **Identify all occurrences** across the documentation  
2. **Analyze usage contexts** to understand meaning and scope
3. **Check for consistency** in how the term is used
4. **Assess definitional need** - would readers benefit from a glossary entry?

### Step 4: Glossary Entry Drafting

#### Entry Structure

Follow the existing glossary format:

```markdown
### Term Name

Brief, clear definition of the term as used in the SPaDE context.

Additional explanation if needed, including:
- Relationship to other glossary terms
- Project-specific usage or meaning
- Key characteristics or properties

#### Variations or Related Terms
- **Related Term 1**: Brief explanation
- **Related Term 2**: Brief explanation
```

#### Content Guidelines

- **Concise but complete** - capture essential meaning without excessive detail
- **SPaDE-specific** - focus on how terms are used within this project
- **Cross-referenced** - link to related existing glossary entries
- **Accessible** - avoid circular definitions or overly technical language
- **Consistent** - match tone and style of existing entries
- **Link to source** - when suitable documentation exists, link the term heading to it

### Step 5: Integration Process

1. **Technical accuracy** - verify definitions are correct
2. **Consistency check** - ensure alignment with existing glossary
3. **Completeness assessment** - confirm all important aspects covered
4. **Style conformance** - match existing glossary formatting and tone
5. **Propose additions** through standard review process
6. **Organize alphabetically** within appropriate sections
7. **Update cross-references** in existing entries as needed
8. **Run glossary linking** (amtd002.md) to add links to new terms throughout documentation

## Tools and Automation

### Recommended Tooling

1. **Term extraction script** to identify candidates automatically
2. **Frequency analysis** to prioritize terms by usage patterns
3. **Context extraction** to gather usage examples for definition drafting
4. **Integration validation** to check proposed entries against existing content

### Output Formats

- **Candidate term list** with frequency and context data
- **Draft glossary entries** in standard markdown format
- **Integration report** documenting rationale and recommendations

## See Also

- [docs/tlad001.md](../tlad001.md) - The SPaDE Glossary
- [docs/admin/amtd002.md](amtd002.md) - Incremental glossary linking task
- [docs/admin/amtd003.md](amtd003.md) - Glossary augmentation task description
- [docs/admin/amms006.md](amms006.md) - Glossary link maintenance
- [docs/admin/amms001.md](amms001.md) - Project structure and naming conventions
