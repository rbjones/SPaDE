#!/usr/bin/env python3
"""
Pipe that extracts only fenced code blocks for a given language from Markdown.

Usage:
    extract_code.py lang < input.md > output.lang
"""

import sys

def main() -> None:
    if len(sys.argv) != 2:
        sys.stderr.write("Usage: strip_formal_text.py <language>\n")
        sys.exit(1)

    language = sys.argv[1].strip()
    if not language:
        sys.stderr.write("Error: language code must be non-empty\n")
        sys.exit(1)

    in_block = False
    emit_block = False
    fence_lang = ""

    for raw_line in sys.stdin:
        line = raw_line.rstrip("\n")

        if line.startswith("```"):
            fence_lang = line[3:].strip().split(None, 1)[0] if len(line) > 3 else ""
            if in_block:
                if emit_block:
                    sys.stdout.write("\n")
                in_block = False
                emit_block = False
            else:
                in_block = True
                emit_block = fence_lang.lower() == language.lower()
            continue

        if in_block and emit_block:
            sys.stdout.write(line + "\n")

if __name__ == "__main__":
    main()