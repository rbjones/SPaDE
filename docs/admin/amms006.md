# Glossary Link Maintenance

This document describes how to maintain glossary links in the SPaDE documentation.

## Overview

The SPaDE project maintains a glossary of important terms in `docs/tlad001.md`. To improve documentation navigability, occurrences of these terms throughout the documentation should link to their glossary definitions.

## Adding Glossary Links

The `amcd001.py` script in this directory automates the process of adding glossary links to the documentation.

### Location

[docs/admin/amcd001.py](./amcd001.py)

### Usage

To preview what changes would be made (dry run):

```bash
cd /path/to/SPaDE
python3 docs/admin/add_glossary_links.py --dry-run
```

To apply the changes:

```bash
cd /path/to/SPaDE
python3 docs/admin/add_glossary_links.py
```

### What the Script Does

The script:

1. Scans all markdown files in the repository (excluding `reviews/` and `retro/` directories)
2. Identifies occurrences of glossary terms defined in `docs/tlad001.md`
3. Adds hyperlinks to the glossary while:
   - Preserving original text capitalization
   - Avoiding terms in code blocks, headings, or existing links
   - Processing longer phrases first to avoid partial matches (e.g., "Focal Tower" before "Focal")
   - Using correct relative paths from each file to the glossary
   - Not modifying the glossary file itself

### Glossary Terms

The script currently links the following 20 terms and their variations:

- Declarative Knowledge
- Deduction / Deductive Engineering
- Diasporic / Diasporic Repository
- Epistemology / Epistemological Stack
- Focal / Focal Intelligence / Focal AI / Focal Engineering / Focal Tower
- The Singularity / Singular Focus
- SPaDE
- Synthetic Epistemology / Synthetic Philosophy
- Terran / Terran Diaspora / Terran Diasporic Repository

### Important Notes

1. **File List Entries**: The script may create nested links in file list entries (e.g., in README.md files where filenames are listed with descriptions). These should be manually reviewed and fixed to restrict the outer link to just the filename portion.

2. **Review Changes**: Always review the changes made by the script before committing them, especially:
   - Check for any nested links that may have been created
   - Verify that links in lists of files are formatted consistently
   - Ensure no unintended links were added

## When to Run the Script

The script should be run:

1. **After adding new glossary terms** to `docs/tlad001.md`
2. **After adding substantial new documentation** that may contain glossary terms
3. **Periodically** (e.g., quarterly) to catch any terms that were added in new content

## Updating the Script

When new terms are added to the glossary:

1. Open `docs/admin/add_glossary_links.py`
2. Update the `TERMS` list with the new term and its anchor
3. Ensure longer phrases are listed before shorter ones to avoid partial matches
4. Test with `--dry-run` before applying changes

## Automation Considerations

### Manual Review Required

Full automation is not recommended because:

1. The script may create nested links in certain contexts (e.g., file lists in README files)
2. Some contexts may require human judgment about whether linking is appropriate
3. Changes should be reviewed for quality and consistency

### Semi-Automated Workflow

A recommended workflow:

1. Run the script with `--dry-run` to see what would change
2. Review the proposed changes
3. Run the script to apply changes
4. Use `git diff` to review all changes
5. Manually fix any nested links or formatting issues
6. Test a sample of links to ensure they work correctly
7. Commit the changes with a descriptive message

### CI/CD Integration

For future consideration, the script could be integrated into CI/CD to:

- **Validation**: Check that existing glossary links are still valid
- **Detection**: Detect new occurrences of glossary terms that aren't linked
- **Reporting**: Generate a report of unlinked glossary terms

However, automatic link addition in CI/CD is not recommended without human review.

## Example

Suppose you add a new term "Metatheory" to the glossary with anchor `#metatheory`.

1. Edit `docs/admin/add_glossary_links.py`:

   ```python
   TERMS = [
       # ... existing terms ...
       ("Metatheory", "#metatheory"),
       # ... more terms ...
   ]
   ```

2. Run a dry-run:

   ```bash
   python3 docs/admin/add_glossary_links.py --dry-run
   ```

3. Review the output to see where "Metatheory" would be linked

4. Apply the changes:

   ```bash
   python3 docs/admin/add_glossary_links.py
   ```

5. Review the changes:

   ```bash
   git diff
   ```

6. Fix any nested links or formatting issues manually

7. Commit:

   ```bash
   git add .
   git commit -m "Add glossary links for new term 'Metatheory'"
   ```

## Troubleshooting

### Script creates nested links

If the script creates nested links (links within link text), these need to be fixed manually. Common locations:

- File lists in README.md files
- Section headings that are also links
- Link text that contains multiple glossary terms

Fix by restricting the outer link to just the filename/essential part, removing the glossary link from the description.

### Links have wrong relative paths

The script calculates relative paths automatically. If you see incorrect paths:

1. Check that the script is run from the repository root directory
2. Verify that `GLOSSARY_PATH = "docs/tlad001.md"` is correct
3. Check for any unusual directory structures

### Some terms are not being linked

Possible causes:

1. The term is in a code block (intentionally skipped)
2. The term is in a heading (intentionally skipped)
3. The term is already in a link (intentionally skipped)
4. The term is not in the `TERMS` list in the script

## See Also

- [docs/tlad001.md](../tlad001.md) - The SPaDE Glossary
- [docs/admin/amtd002.md](amtd002.md) - Task description for glossary link augmentation
- [reviews/20251023-1356-copilot-glossary-links.md](../../reviews/20251023-1356-copilot-glossary-links.md) - Initial glossary linking review report
