# MCP Subsystem (mcp)

This directory contains the Model Context Protocol (MCP) server implementation for SPaDE.
The principle SPaDE MCP server is implemented in Python and makes available the functionality delivered by the kr, dk and di subsystems.
Because of the AI oriented development strategy, we may wish to create other MCP servers available to LLMs so that they can fully contribute to the development.

The first of these might be an MCP server for ProofPower, and/or NOL4, since those systems are likely to be used during the early work on the logical foundations and their metatheory, which would then be imported into SPaDE repositories.

The content of thid directory falls under the following headings"

- **[Code](#code)**
- **[Testing and Evaluation](#testing-and-evaluation)**

## Code

- [mcpcd001.py](mcpcd001.py) - Main SPaDE MCP server implementation
- [mcpcd002.py](mcpcd002.py) - Minimal/Debug MCP server
- [mcpcd003.sh](mcpcd003.sh) - Debug wrapper script for running the server

## Testing and Evaluation

- [mcpte001.py](mcpte001.py) - Integration tests for the MCP server

