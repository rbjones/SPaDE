#!/usr/bin/env python3
"""
Glossary Term Discovery Script
===============================

This script identifies potential terms for glossary augmentation by scanning
SPaDE documentation for technical terminology not yet in the glossary.

Usage:
    python3 amcd003.py [OPTIONS]

Options:
    --min-frequency N    Minimum frequency (default: 2)
    --min-files N        Minimum number of files (default: 2)
    --output FORMAT      Output format: 'text' (default), 'json', 'markdown'
    --context-lines N    Number of context lines to show (default: 1)
    --exclude-common     Exclude common English words (default: True)

The script:
1. Scans all markdown files (excluding reviews/, retro/, tools/ and glossary)
2. Extracts potential technical terms using linguistic patterns
3. Filters by frequency and importance
4. Outputs candidate list with usage contexts

Term Discovery Patterns:
- Capitalized phrases (2-4 words)
- Technical compounds (e.g., "knowledge repository")
- Domain-specific terminology
- Project-specific concepts
"""

import re
import os
import sys
import json
from pathlib import Path
from collections import defaultdict

# Import term extraction to get existing glossary terms
from amcd002 import extract_glossary_terms

GLOSSARY_PATH = "docs/tlad001.md"

# Common words to exclude (extend as needed)
COMMON_WORDS = {
    'the', 'a', 'an', 'and', 'or', 'but', 'in', 'on', 'at', 'to', 'for',
    'of', 'with', 'by', 'from', 'up', 'about', 'into', 'through', 'during',
    'before', 'after', 'above', 'below', 'between', 'under', 'again', 'further',
    'then', 'once', 'here', 'there', 'when', 'where', 'why', 'how', 'all', 'both',
    'each', 'few', 'more', 'most', 'other', 'some', 'such', 'only', 'own', 'same',
    'so', 'than', 'too', 'very', 'can', 'will', 'just', 'should', 'now',
    'github', 'markdown', 'readme', 'license', 'contributing', 'issue', 'pull',
    'request', 'commit', 'branch', 'repository', 'file', 'directory', 'section',
    'document', 'documentation', 'page', 'link', 'see', 'also', 'note', 'example',
    'chapter', 'introduction', 'conclusion', 'summary', 'overview', 'description',
    'copilot', 'review', 'report', 'date', 'time', 'author', 'task', 'step'
}


def get_markdown_files():
    """Get all markdown files in scope."""
    md_files = []
    for root, dirs, files in os.walk('.'):
        # Skip excluded directories
        dirs[:] = [
            d for d in dirs
            if not d.startswith('.')
            and d not in ['reviews', 'retro', 'tools', 'node_modules']
        ]
        
        for file in files:
            if file.endswith('.md'):
                filepath = os.path.join(root, file)
                # Skip the glossary itself
                if filepath.replace('./', '') != GLOSSARY_PATH:
                    md_files.append(filepath)
    
    return sorted(md_files)


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
    """Check if position is inside a markdown link."""
    # Look backwards and forwards for link syntax
    start = max(0, position - 200)
    end = min(len(content), position + 200)
    
    before = content[start:position]
    after = content[position:end]
    
    # Check for link patterns [text](url)
    if '](' in before[-50:] and ')' in after[:50]:
        return True
    if '[' in before[-50:] and ']' not in before[-50:]:
        return True
    if '(' in before[-50:] and ')' not in before[-50:]:
        return True
    
    return False


def extract_candidate_terms(content, filepath):
    """Extract potential technical terms from content."""
    candidates = []
    
    # Pattern 1: Capitalized phrases (2-4 words) - must start with uppercase
    # Example: "Knowledge Repository", "Deductive Kernel"
    pattern1 = re.compile(r'\b([A-Z][a-z]+(?:\s+[A-Z][a-z]+){1,3})\b')
    
    # Pattern 2: Technical compounds with common technical words
    # Example: "logical system", "semantic model"
    # This pattern matches technical terms (like "logical", "semantic", etc.)
    # followed by a noun, or a noun followed by a technical term.
    # The negative lookbehind (?<!\bthe\s) prevents matching phrases starting with "the"
    technical_words = r'(?:logical|semantic|syntactic|abstract|concrete|formal|informal|' \
                     r'meta|object|type|proof|theorem|axiom|inference|model|system|' \
                     r'language|theory|framework|architecture|structure|component|' \
                     r'interface|implementation|specification|definition|representation|' \
                     r'kernel|repository|engine|mechanism|protocol|methodology)'
    
    # Build pattern: technical_word + space + noun OR noun + space + technical_word
    # Exclude patterns starting with articles (the, a, an)
    pattern2 = re.compile(
        r'(?<!\bthe\s)(?<!\ba\s)(?<!\ban\s)\b(' + 
        technical_words + r'\s+(?:[a-z]+|[A-Z][a-z]+)|(?:[a-z]+|[A-Z][a-z]+)\s+' + 
        technical_words + r')\b',
        re.IGNORECASE
    )
    
    # Pattern 3: Hyphenated technical terms
    # Example: "proof-checker", "meta-language"
    pattern3 = re.compile(r'\b([a-z]+-[a-z]+(?:-[a-z]+)?)\b', re.IGNORECASE)
    
    # Extract matches
    for pattern in [pattern1, pattern2, pattern3]:
        for match in pattern.finditer(content):
            pos = match.start()
            
            # Skip if in code block or link
            if is_in_code_block(content, pos) or is_in_link(content, pos):
                continue
            
            term = match.group(1).strip()
            
            # Skip if starts with article or common word
            if term.lower().split()[0] in COMMON_WORDS:
                continue
            
            # Get context (surrounding line)
            line_start = content.rfind('\n', 0, pos) + 1
            line_end = content.find('\n', pos)
            if line_end == -1:
                line_end = len(content)
            
            context = content[line_start:line_end].strip()
            
            candidates.append({
                'term': term,
                'context': context,
                'file': filepath,
                'position': pos
            })
    
    return candidates


def filter_candidates(candidates, existing_terms, min_frequency=2, min_files=2, exclude_common=True):
    """Filter and aggregate candidate terms."""
    # Normalize existing terms for comparison (supports tuples of length 2 or 3)
    existing_lower = set(t[0].lower() for t in existing_terms)
    
    # Aggregate by normalized term
    term_data = defaultdict(lambda: {
        'occurrences': [],
        'files': set(),
        'contexts': []
    })
    
    for candidate in candidates:
        term = candidate['term']
        term_lower = term.lower()
        
        # Skip if already in glossary
        if term_lower in existing_lower:
            continue
        
        # Skip if too short
        if len(term) < 3:
            continue
        
        # Skip if all common words (if exclude_common)
        if exclude_common:
            words = term_lower.split()
            if all(w in COMMON_WORDS for w in words):
                continue
        
        # Add to aggregated data
        term_data[term_lower]['occurrences'].append(candidate)
        term_data[term_lower]['files'].add(candidate['file'])
        if len(term_data[term_lower]['contexts']) < 3:  # Keep up to 3 contexts
            term_data[term_lower]['contexts'].append({
                'context': candidate['context'],
                'file': candidate['file']
            })
    
    # Filter by frequency and file count
    filtered = {}
    for term_lower, data in term_data.items():
        frequency = len(data['occurrences'])
        file_count = len(data['files'])
        
        if frequency >= min_frequency and file_count >= min_files:
            # Use the most common capitalization
            term_variants = [occ['term'] for occ in data['occurrences']]
            most_common_term = max(set(term_variants), key=term_variants.count)
            
            filtered[most_common_term] = {
                'frequency': frequency,
                'file_count': file_count,
                'files': sorted(data['files']),
                'contexts': data['contexts']
            }
    
    return filtered


def format_output(candidates, format='text'):
    """Format candidate terms for output."""
    if format == 'json':
        return json.dumps(candidates, indent=2)
    
    elif format == 'markdown':
        output = "# Glossary Term Candidates\n\n"
        output += f"Found {len(candidates)} potential terms for glossary augmentation.\n\n"
        
        # Sort by frequency
        sorted_terms = sorted(candidates.items(), key=lambda x: x[1]['frequency'], reverse=True)
        
        for term, data in sorted_terms:
            output += f"## {term}\n\n"
            output += f"**Frequency**: {data['frequency']} occurrences in {data['file_count']} files\n\n"
            output += "**Files**:\n"
            for file in data['files'][:5]:  # Show up to 5 files
                output += f"- {file}\n"
            if len(data['files']) > 5:
                output += f"- ... and {len(data['files']) - 5} more\n"
            output += "\n**Example contexts**:\n"
            for ctx in data['contexts']:
                output += f"- `{ctx['context']}` (in {ctx['file']})\n"
            output += "\n---\n\n"
        
        return output
    
    else:  # text format
        output = []
        output.append(f"Glossary Term Candidates ({len(candidates)} found)")
        output.append("=" * 60)
        output.append("")
        
        # Sort by frequency
        sorted_terms = sorted(candidates.items(), key=lambda x: x[1]['frequency'], reverse=True)
        
        for term, data in sorted_terms:
            output.append(f"{term}")
            output.append(f"  Frequency: {data['frequency']} occurrences in {data['file_count']} files")
            output.append(f"  Files: {', '.join(data['files'][:3])}")
            if len(data['files']) > 3:
                output.append(f"         ... and {len(data['files']) - 3} more")
            output.append("  Example contexts:")
            for ctx in data['contexts'][:2]:
                output.append(f"    - {ctx['context'][:80]}...")
                output.append(f"      (in {ctx['file']})")
            output.append("")
        
        return '\n'.join(output)


def main():
    import argparse
    
    parser = argparse.ArgumentParser(description='Discover potential glossary terms')
    parser.add_argument('--min-frequency', type=int, default=2,
                       help='Minimum frequency (default: 2)')
    parser.add_argument('--min-files', type=int, default=2,
                       help='Minimum number of files (default: 2)')
    parser.add_argument('--output', choices=['text', 'json', 'markdown'], default='text',
                       help='Output format (default: text)')
    parser.add_argument('--context-lines', type=int, default=1,
                       help='Number of context lines (default: 1)')
    parser.add_argument('--include-common', action='store_true',
                       help='Include common words (default: exclude)')
    
    args = parser.parse_args()
    
    # Load existing glossary terms
    print("Loading existing glossary terms...", file=sys.stderr)
    try:
        existing_terms = extract_glossary_terms()
        print(f"Found {len(existing_terms)} existing terms", file=sys.stderr)
    except Exception as e:
        print(f"Error loading glossary: {e}", file=sys.stderr)
        sys.exit(1)
    
    # Get all markdown files
    md_files = get_markdown_files()
    print(f"Scanning {len(md_files)} files...", file=sys.stderr)
    
    # Extract candidate terms from all files
    all_candidates = []
    for filepath in md_files:
        try:
            with open(filepath, 'r', encoding='utf-8') as f:
                content = f.read()
            candidates = extract_candidate_terms(content, filepath)
            all_candidates.extend(candidates)
        except Exception as e:
            print(f"Warning: Error processing {filepath}: {e}", file=sys.stderr)
    
    print(f"Found {len(all_candidates)} candidate term occurrences", file=sys.stderr)
    
    # Filter and aggregate
    filtered = filter_candidates(
        all_candidates,
        existing_terms,
        min_frequency=args.min_frequency,
        min_files=args.min_files,
        exclude_common=not args.include_common
    )
    
    print(f"Filtered to {len(filtered)} unique candidate terms", file=sys.stderr)
    print("", file=sys.stderr)
    
    # Output results
    output = format_output(filtered, args.output)
    print(output)


if __name__ == '__main__':
    main()
