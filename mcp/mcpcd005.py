"""MCP server for the reference-based T-expression repository prototype."""

import argparse
import json
import os
import sys

from mcp.server.fastmcp import FastMCP

workspace_root = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
if workspace_root not in sys.path:
    sys.path.insert(0, workspace_root)

from kr.krcd009 import LowLevelIO, StaleCacheError  # noqa: E402
from kr.krcd014 import TExpressions  # noqa: E402


server = FastMCP(
    "SPaDE-T-expression-server",
    host=os.getenv("SPADE_MCP_HOST", "127.0.0.1"),
    port=int(os.getenv("SPADE_MCP_PORT", "8000")),
    mount_path=os.getenv("SPADE_MCP_MOUNT_PATH", "/"),
    sse_path=os.getenv("SPADE_MCP_SSE_PATH", "/sse"),
)


def _validate_tree(tree):
    if not isinstance(tree, dict) or set(tree) != {"label", "children"}:
        raise ValueError("Each node must have exactly 'label' and 'children' fields")
    if not isinstance(tree["label"], str) or not isinstance(tree["children"], list):
        raise ValueError("Node label must be a string and children must be a list")
    tree["label"].encode("utf-8")
    for child in tree["children"]:
        _validate_tree(child)


def _write_tree(trees, tree):
    children = [_write_tree(trees, child) for child in tree["children"]]
    return trees.write_node(tree["label"].encode("utf-8"), children)


def _read_tree(trees, seq_num):
    node = trees.read_node(seq_num)
    return {
        "label": node.label.decode("utf-8"),
        "children": [_read_tree(trees, child) for child in node.children],
    }


@server.tool()
async def create_repository(filepath: str, version: int = 1) -> str:
    """Create a repository at filepath with the specified version."""
    io = LowLevelIO()
    try:
        io.open_new_repository(filepath, version=version)
    finally:
        io.close_repository()
    return f"Successfully created repository at {filepath} with version {version}"


@server.tool()
async def write_texpression(filepath: str, tree_json: str) -> str:
    """Write a JSON tree of UTF-8 string labels and ordered children.

    Each node must have the form {"label": "text", "children": []}.
    Returns the root sequence number; identical nodes are shared.
    """
    tree = json.loads(tree_json)
    _validate_tree(tree)
    io = LowLevelIO()
    try:
        io.open_existing_repository_read(filepath)
        io.open_existing_repository_append(filepath)
        seq_num = _write_tree(TExpressions(io), tree)
    except StaleCacheError as exc:
        raise RuntimeError("Repository was modified by another process. Please retry.") from exc
    finally:
        io.close_repository()
    return f"Successfully wrote T-expression. Sequence Number: {seq_num}"


@server.tool()
async def read_texpression(filepath: str, seq_num: int) -> str:
    """Read a T-expression tree as JSON; all labels must be valid UTF-8."""
    io = LowLevelIO()
    try:
        io.open_existing_repository_read(filepath)
        return json.dumps(_read_tree(TExpressions(io), seq_num))
    finally:
        io.close_repository()


def main():
    parser = argparse.ArgumentParser(description="SPaDE T-expression MCP server")
    parser.add_argument(
        "--transport", choices=["stdio", "sse", "streamable-http"],
        default=os.getenv("SPADE_MCP_TRANSPORT", "stdio"),
    )
    parser.add_argument("--host", default=os.getenv("SPADE_MCP_HOST", "127.0.0.1"))
    parser.add_argument("--port", type=int, default=os.getenv("SPADE_MCP_PORT", "8000"))
    parser.add_argument("--mount-path", default=os.getenv("SPADE_MCP_MOUNT_PATH", "/"))
    parser.add_argument("--sse-path", default=os.getenv("SPADE_MCP_SSE_PATH", "/sse"))
    args = parser.parse_args()
    server.settings.host = args.host
    server.settings.port = args.port
    server.settings.mount_path = args.mount_path
    server.settings.sse_path = args.sse_path
    server.run(transport=args.transport, mount_path=args.mount_path)


if __name__ == "__main__":
    main()
