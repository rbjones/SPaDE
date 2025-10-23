#!/usr/bin/env python3
"""
Add Glossary Links Script
==========================

This script adds hyperlinks from glossary terms throughout the SPaDE documentation
to their definitions in the project glossary (docs/tlad001.md).

Usage:
    python3 add_glossary_links.py [--dry-run]

Options:
    --dry-run    Show what changes would be made without modifying files

The script:
1. Scans all markdown files in the repository (excluding reviews/ and retro/)
2. Identifies occurrences of glossary terms
3. Adds hyperlinks to the glossary while:
   - Preserving original text capitalization
   - Avoiding terms in code blocks, headings, or existing links
   - Processing longer phrases first to avoid partial matches
   - Using correct relative paths from each file to the glossary

Glossary terms are defined in TERMS list below.
"""

import re
import os
from pathlib import Path

# Define the glossary path
GLOSSARY_PATH = "docs/tlad001.md"

# Terms to search for (in order of specificity - longer phrases first)
# This ensures we match "Terran Diasporic Repository" before "Terran"
TERMS = [
    ("Terran Diasporic Repository", "#terran"),
    ("Terran Diaspora", "#terran"),
    ("Diasporic Repository", "#diasporic"),
    ("Focal Intelligence", "#focal-intelligence-or-focal-ai"),
    ("Focal AI", "#focal-intelligence-or-focal-ai"),
    ("Focal Engineering", "#focal-engineering"),
    ("Focal Tower", "#focal-tower"),
    ("Declarative Knowledge", "#declarative-knowledge"),
    ("Deductive Engineering", "#deductive-engineering"),
    ("Epistemological Stack", "#epistemological-stack"),
    ("Synthetic Epistemology", "#synthetic-epistemology"),
    ("Synthetic Philosophy", "#synthetic-philosophy"),
    ("Singular Focus", "#singular-focus"),
    ("The Singularity", "#the-singularity"),
    ("Deduction", "#deduction"),
    ("Diasporic", "#diasporic"),
    ("Epistemology", "#epistemology"),
    ("Focal", "#focal"),
    ("SPaDE", "#spade"),
    ("Terran", "#terran"),
]

def get_relative_path_to_glossary(from_file):
    """Calculate relative path from a file to the glossary."""
    from_dir = Path(from_file).parent
    glossary_path = Path(GLOSSARY_PATH)
    
    # Calculate the relative path
    try:
        rel_path = os.path.relpath(glossary_path, from_dir)
        return rel_path.replace('\\', '/')  # Normalize for markdown
    except ValueError:
        # If on different drives on Windows
        return GLOSSARY_PATH

def is_in_code_block(content, position):
    """Check if position is inside a code block."""
    # Find all code blocks
    code_blocks = []
    # Triple backticks
    for match in re.finditer(r'```.*?```', content, re.DOTALL):
        code_blocks.append((match.start(), match.end()))
    # Inline code
    for match in re.finditer(r'`[^`]+`', content):
        code_blocks.append((match.start(), match.end()))
    
    for start, end in code_blocks:
        if start <= position < end:
            return True
    return False

def is_in_link(content, position):
    """Check if position is inside an existing markdown link."""
    # Look backwards and forwards for link syntax
    start = max(0, position - 200)
    end = min(len(content), position + 200)
    
    # Get the context
    before = content[start:position]
    after = content[position:end]
    
    # Check for various link patterns
    # [text](url)
    if '](' in before[-50:] and ')' in after[:50]:
        # Find the opening [
        bracket_count = 0
        for i in range(len(before) - 1, -1, -1):
            if before[i] == ']':
                bracket_count += 1
            elif before[i] == '[':
                bracket_count -= 1
                if bracket_count < 0:
                    return True
    
    # Inside [text] part
    if '[' in before[-50:] and ']' not in before[-50:]:
        return True
    
    # Inside (url) part  
    if '(' in before[-50:] and ')' not in before[-50:]:
        return True
        
    return False

def is_in_heading(content, position):
    """Check if position is in a heading (we want to preserve headings)."""
    # Find the line containing this position
    line_start = content.rfind('\n', 0, position) + 1
    line_end = content.find('\n', position)
    if line_end == -1:
        line_end = len(content)
    
    line = content[line_start:line_end]
    # Check if line starts with #
    return line.lstrip().startswith('#')

def add_links_to_file(filepath, dry_run=False):
    """Add glossary links to a file."""
    with open(filepath, 'r', encoding='utf-8') as f:
        content = f.read()
    
    original_content = content
    rel_glossary_path = get_relative_path_to_glossary(filepath)
    
    changes_made = 0
    
    # Track positions that have been linked to avoid overlapping replacements
    linked_positions = set()
    
    # Process terms in order (longest first to avoid partial matches)
    for term, anchor in TERMS:
        # Case-insensitive search
        pattern = re.compile(re.escape(term), re.IGNORECASE)
        
        matches = list(pattern.finditer(content))
        
        for match in reversed(matches):  # Process from end to start to maintain positions
            pos = match.start()
            
            # Skip if we've already processed overlapping content
            if any(pos <= p < pos + len(term) for p in linked_positions):
                continue
            
            # Skip if in code block, existing link, or heading
            if is_in_code_block(content, pos):
                continue
            if is_in_link(content, pos):
                continue
            if is_in_heading(content, pos):
                continue
            
            # Get the actual matched text (preserving case)
            matched_text = match.group()
            
            # Create the link
            link = f"[{matched_text}]({rel_glossary_path}{anchor})"
            
            # Replace
            content = content[:pos] + link + content[pos + len(matched_text):]
            
            # Mark this position range as linked
            for i in range(pos, pos + len(matched_text)):
                linked_positions.add(i)
            
            changes_made += 1
    
    if changes_made > 0 and not dry_run:
        with open(filepath, 'w', encoding='utf-8') as f:
            f.write(content)
    
    return changes_made

def main():
    import sys
    
    dry_run = '--dry-run' in sys.argv
    
    # Find all markdown files
    md_files = []
    for root, dirs, files in os.walk('.'):
        # Skip excluded directories
        dirs[:] = [d for d in dirs if not d.startswith('.') and d not in ['reviews', 'retro']]
        
        for file in files:
            if file.endswith('.md'):
                filepath = os.path.join(root, file)
                # Skip the glossary itself
                if filepath.replace('./', '') != GLOSSARY_PATH:
                    md_files.append(filepath)
    
    md_files.sort()
    
    print(f"Processing {len(md_files)} files...")
    if dry_run:
        print("(Dry run - no files will be modified)")
    print()
    
    total_changes = 0
    for filepath in md_files:
        changes = add_links_to_file(filepath, dry_run)
        if changes > 0:
            print(f"{filepath}: {changes} links added")
            total_changes += changes
    
    print(f"\nTotal links added: {total_changes}")

if __name__ == '__main__':
    main()
