#!/usr/bin/env python3
"""
Glossary Term Extraction Script
================================

This script parses the SPaDE glossary (docs/tlad001.md) to dynamically extract
all terms and their anchor links.

Usage:
    python3 amcd002.py [--output FORMAT]

Options:
    --output FORMAT    Output format: 'python' (default), 'json', 'text'

The script extracts:
- Primary terms from ### headers
- Variations from - **Term**: list items
- Variations from - **[Term](...)** patterns
- #### headers if used for term variations (per linting guidelines)

Terms are sorted by length (longest first) to ensure compound terms are
processed before their component parts.

Output formats:
- python: Python list of tuples [(term, anchor), ...]
- json: JSON array of objects [{"term": "...", "anchor": "..."}, ...]
- text: Plain text, one term per line with tab-separated anchor
"""

import re
import json
from pathlib import Path

GLOSSARY_PATH = Path(__file__).parent.parent.parent / "docs" / "tlad001.md"


def generate_anchor(text):
    """Generate GitHub-compatible anchor from heading text."""
    # Remove markdown links but keep the text
    text = re.sub(r'\[([^\]]+)\]\([^\)]+\)', r'\1', text)
    
    # Convert to lowercase
    anchor = text.lower()
    
    # Replace spaces and special characters with hyphens
    anchor = re.sub(r'[^\w\s-]', '', anchor)
    anchor = re.sub(r'[-\s]+', '-', anchor)
    
    # Remove leading/trailing hyphens
    anchor = anchor.strip('-')
    
    return '#' + anchor


def extract_glossary_terms(glossary_path=None):
    """
    Extract all glossary terms and their anchors from the glossary file.
    
    Returns:
        List of tuples [(term, anchor), ...] sorted by term length (longest first)
    """
    if glossary_path is None:
        glossary_path = GLOSSARY_PATH
    
    with open(glossary_path, 'r', encoding='utf-8') as f:
        content = f.read()
    
    terms = []
    
    # Track the current section for context
    current_section = None
    
    lines = content.split('\n')
    i = 0
    
    while i < len(lines):
        line = lines[i]
        
        # Primary terms from ### headers
        if line.startswith('### '):
            term_text = line[4:].strip()
            
            # Check if it's a link: ### [Term](url)
            link_match = re.match(r'\[([^\]]+)\]\(([^\)]+)\)', term_text)
            if link_match:
                term = link_match.group(1)
                # For linked headings, use the heading text but generate anchor
                anchor = generate_anchor(term)
            else:
                term = term_text
                anchor = generate_anchor(term)
            
            terms.append((term, anchor))
            current_section = anchor
        
        # Term variations from #### headers
        elif line.startswith('#### '):
            term_text = line[5:].strip()
            
            # Check if it's a link
            link_match = re.match(r'\[([^\]]+)\]\(([^\)]+)\)', term_text)
            if link_match:
                term = link_match.group(1)
                anchor = generate_anchor(term)
            else:
                term = term_text
                anchor = generate_anchor(term)
            
            terms.append((term, anchor))
        
        # Variations from list items: - **Term**: or - **[Term](...)**: or - **[Term](...)**
        elif line.strip().startswith('- **'):
            # Pattern: - **Term**: or - **Term**
            match1 = re.match(r'-\s+\*\*([^\*]+)\*\*:', line.strip())
            if match1:
                term = match1.group(1)
                # For list items, use the current section anchor
                if current_section:
                    terms.append((term, current_section))
                    # Also extract parts if it's a compound "X or Y" term
                    if ' or ' in term:
                        parts = [p.strip() for p in term.split(' or ')]
                        for part in parts:
                            terms.append((part, current_section))
            else:
                # Pattern: - **[Term](...)**:  or - **[Term](...)**
                match2 = re.match(r'-\s+\*\*\[([^\]]+)\]\([^\)]+\)\*\*:?', line.strip())
                if match2:
                    term = match2.group(1)
                    if current_section:
                        terms.append((term, current_section))
        
        i += 1
    
    # Remove duplicates while preserving order
    seen = set()
    unique_terms = []
    for term, anchor in terms:
        key = (term.lower(), anchor)
        if key not in seen:
            seen.add(key)
            unique_terms.append((term, anchor))
    
    # Sort by term length (longest first) to handle compound terms correctly
    unique_terms.sort(key=lambda x: len(x[0]), reverse=True)
    
    return unique_terms


def format_output(terms, format='python'):
    """Format terms for output in specified format."""
    if format == 'python':
        # Python list of tuples format
        output = "TERMS = [\n"
        for term, anchor in terms:
            # Escape quotes in term
            term_escaped = term.replace('"', '\\"')
            output += f'    ("{term_escaped}", "{anchor}"),\n'
        output += "]\n"
        return output
    
    elif format == 'json':
        # JSON format
        terms_list = [{"term": term, "anchor": anchor} for term, anchor in terms]
        return json.dumps(terms_list, indent=2)
    
    elif format == 'text':
        # Plain text format
        output = []
        for term, anchor in terms:
            output.append(f"{term}\t{anchor}")
        return '\n'.join(output)
    
    else:
        raise ValueError(f"Unknown format: {format}")


def main():
    import sys
    
    # Parse command line arguments
    output_format = 'python'
    if '--output' in sys.argv:
        idx = sys.argv.index('--output')
        if idx + 1 < len(sys.argv):
            output_format = sys.argv[idx + 1]
    
    # Extract terms
    try:
        terms = extract_glossary_terms()
        
        # Output in requested format
        output = format_output(terms, output_format)
        print(output)
        
        # Also print statistics to stderr
        import sys
        print(f"Extracted {len(terms)} unique terms from glossary", file=sys.stderr)
        
    except FileNotFoundError:
        print(f"Error: Glossary file not found at {GLOSSARY_PATH}", file=sys.stderr)
        sys.exit(1)
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)


if __name__ == '__main__':
    main()
