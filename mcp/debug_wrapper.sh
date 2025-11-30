#!/bin/bash
LOGfile="/Users/rbj/git/SPaDE/mcp/wrapper.log"
echo "--- Starting wrapper at $(date) ---" >> "$LOGfile"
echo "CWD: $(pwd)" >> "$LOGfile"
echo "Python: /Users/rbj/git/SPaDE/.venv/bin/python" >> "$LOGfile"
echo "Script: /Users/rbj/git/SPaDE/mcp/spade-mcp/src/spade_server.py" >> "$LOGfile"

/Users/rbj/git/SPaDE/.venv/bin/python /Users/rbj/git/SPaDE/mcp/spade-mcp/src/spade_server.py 2>> "$LOGfile"
