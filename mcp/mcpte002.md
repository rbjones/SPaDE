# MCP Copilot Access (mcpte002)

This note explains how to start the SPaDE MCP server for use by Copilot (or any MCP client) and how to perform a quick connectivity test.

## Prerequisites
- Python 3 installed in the dev container (already present).
- Workspace root on `PYTHONPATH` so the server can import the `kr` modules.
- Dependencies from `requirements.txt` are baked into the container build; only re-run `pip install -r requirements.txt` if you are outside the dev container or after adding new requirements.

## Start the server
- From `mcp/`, launch the server in the foreground:
  - `make serve`
- The target sets `PYTHONPATH=..` and runs `python3 mcpcd001.py`.
- Logs are written to `mcp/server.log` and `/tmp/spade_server_startup.log` during startup.

## Connect with an MCP client (Copilot)
- Configure your MCP-enabled client to start the server via the `make serve` command (or `python3 mcpcd001.py` with `PYTHONPATH=..`).
- The server name is `SPaDE-server` and exposes three tools:
  - `create_repository(filepath, version=1)`
  - `write_sexpression(filepath, sexp_json)`
  - `read_sexpression(filepath, seq_num)`
- Communication is over stdio (no sockets), so clients should launch the process directly.

## Smoke test (optional)
- Run the integration harness from `mcp/` to validate the server:
  - `PYTHONPATH=.. python3 mcpte001.py`
- The harness initializes the server, lists tools, and exercises `create_repository`, `write_sexpression`, and `read_sexpression` end-to-end.
