#!/bin/bash
# Wrapper script for debugging the MCP server
# Usage: ./mcpcd003.sh

# Determine the directory where this script is located
SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
WORKSPACE_ROOT="$(dirname "$SCRIPT_DIR")"
LOGfile="$SCRIPT_DIR/wrapper.log"

echo "--- Starting wrapper at $(date) ---" >> "$LOGfile"
echo "CWD: $(pwd)" >> "$LOGfile"
echo "Python: $(which python3)" >> "$LOGfile"
echo "Script: $SCRIPT_DIR/mcpcd001.py" >> "$LOGfile"

# Run the server using the system python3 (from container)
python3 "$SCRIPT_DIR/mcpcd001.py" 2>> "$LOGfile"
