# MCP Copilot Access (mcpte002)

This note explains how to start the SPaDE MCP server for use by Copilot (or any MCP client) and how to perform a quick connectivity test.

## Prerequisites
- Python 3 installed in the dev container (already present).
- Workspace root on `PYTHONPATH` so the server can import the `kr` modules.
- Dependencies from `requirements.txt` are baked into the container build; only re-run `pip install -r requirements.txt` if you are outside the dev container or after adding new requirements.

## Start the server
- From `mcp/`, launch the server in the foreground:
  - `make serve`
- By default, the server uses stdio, preserving compatibility with clients that
  launch it as a subprocess. The target sets `PYTHONPATH=..`.
- To use SSE instead, run `make serve MCP_TRANSPORT=sse`. The default HTTP
  address is `127.0.0.1:8000`.
- The server can also be configured with `--transport`, `--host`, `--port`,
  `--mount-path`, and `--sse-path` when run directly. The corresponding
  environment variables are `SPADE_MCP_TRANSPORT`, `SPADE_MCP_HOST`,
  `SPADE_MCP_PORT`, `SPADE_MCP_MOUNT_PATH`, and `SPADE_MCP_SSE_PATH`.
  Command-line options take precedence over environment variables; Make
  variables such as `MCP_PORT` are passed as command-line options.
- Logs are written to `mcp/server.log` and `/tmp/spade_server_startup.log` during startup.

## Connect with an MCP client (Copilot)
- Configure your MCP-enabled client to start the server via the `make serve` command (or `python3 mcpcd001.py` with `PYTHONPATH=..`).
- The server name is `SPaDE-server` and exposes three tools:
  - `create_repository(filepath, version=1)`
  - `write_sexpression(filepath, sexp_json)`
  - `read_sexpression(filepath, seq_num)`
- With the default stdio transport, clients should launch the process directly.
  With SSE, connect to `http://127.0.0.1:8000/sse` unless the server paths or
  address have been configured differently.

## Smoke test (optional)
- Run the integration harness from `mcp/` to validate the server:
  - `PYTHONPATH=.. python3 mcpte001.py`
- The harness checks stdio and SSE connectivity, exercises
  `create_repository`, `write_sexpression`, and `read_sexpression`, and retains
  the repository round-trip and repeated-content checks.
