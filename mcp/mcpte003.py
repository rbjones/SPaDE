"""MCP integration tests for the T-expression server."""

import json
import os
import re
import socket
import subprocess
import sys
import time
from contextlib import asynccontextmanager
from pathlib import Path

import anyio
import pytest
from mcp import ClientSession, StdioServerParameters
from mcp.client.sse import sse_client
from mcp.client.stdio import stdio_client

ROOT = Path(__file__).resolve().parent.parent
SERVER = ROOT / "mcp" / "mcpcd005.py"
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from kr.krcd009 import LowLevelIO  # noqa: E402
from kr.krcd014 import TExpressions  # noqa: E402


@asynccontextmanager
async def connected_session(transport):
    env = os.environ.copy()
    env["PYTHONPATH"] = str(ROOT) + os.pathsep + env.get("PYTHONPATH", "")
    env["SPADE_MCP_TRANSPORT"] = "stdio"
    env["SPADE_MCP_HOST"] = "127.0.0.1"
    env["SPADE_MCP_MOUNT_PATH"] = "/"
    env["SPADE_MCP_SSE_PATH"] = "/sse"
    if transport == "stdio":
        parameters = StdioServerParameters(command=sys.executable, args=[str(SERVER)], env=env)
        async with stdio_client(parameters) as streams:
            async with ClientSession(*streams) as session:
                await session.initialize()
                yield session
    else:
        with socket.socket() as sock:
            sock.bind(("127.0.0.1", 0))
            port = sock.getsockname()[1]
        process = subprocess.Popen(
            [sys.executable, str(SERVER), "--transport", "sse", "--port", str(port)],
            env=env, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
        )
        try:
            deadline = time.monotonic() + 10
            while True:
                if process.poll() is not None:
                    raise RuntimeError(f"SSE server exited with status {process.returncode}")
                try:
                    with socket.create_connection(("127.0.0.1", port), timeout=0.2):
                        break
                except OSError:
                    if time.monotonic() >= deadline:
                        raise TimeoutError("SSE server did not start")
                    await anyio.sleep(0.1)
            async with sse_client(f"http://127.0.0.1:{port}/sse") as streams:
                async with ClientSession(*streams) as session:
                    await session.initialize()
                    yield session
        finally:
            process.terminate()
            try:
                process.wait(timeout=5)
            except subprocess.TimeoutExpired:
                process.kill()
                process.wait(timeout=5)


def text(result):
    return next(item.text for item in result.content if item.type == "text")


async def exercise_server(transport, path):
    tree = {
        "label": "root \u00e9 \u0000\u0001",
        "children": [
            {"label": "", "children": []},
            {"label": "branch", "children": [
                {"label": "shared", "children": []},
                {"label": "shared", "children": []},
            ]},
            {"label": "shared", "children": []},
        ],
    }
    async with connected_session(transport) as session:
        tools = await session.list_tools()
        assert {tool.name for tool in tools.tools} == {
            "create_repository", "write_texpression", "read_texpression"
        }
        created = await session.call_tool("create_repository", {"filepath": str(path)})
        assert not created.isError

        async def write(value):
            return await session.call_tool(
                "write_texpression", {"filepath": str(path), "tree_json": value}
            )

        written = await write(json.dumps(tree))
        assert not written.isError, text(written)
        match = re.search(r"Sequence Number: (\d+)", text(written))
        assert match
        root = int(match.group(1))
        read = await session.call_tool(
            "read_texpression", {"filepath": str(path), "seq_num": root}
        )
        assert not read.isError, text(read)
        assert json.loads(text(read)) == tree

        before = path.read_bytes()
        repeated = await write(json.dumps(tree))
        assert not repeated.isError
        assert text(repeated) == text(written)
        assert path.read_bytes() == before

        io = LowLevelIO()
        try:
            io.open_existing_repository_read(str(path))
            nodes = TExpressions(io)
            parent = nodes.read_node(root)
            branch = nodes.read_node(parent.children[1])
            assert branch.children == [parent.children[2], parent.children[2]]
        finally:
            io.close_repository()

        for invalid in (
            "not JSON",
            json.dumps({"label": "root", "children": [{"label": 1, "children": []}]}),
            json.dumps({"label": "root", "children": [], "extra": 1}),
            json.dumps({"label": "\ud800", "children": []}),
        ):
            result = await write(invalid)
            assert result.isError, text(result)
            assert path.read_bytes() == before
        invalid_read = await session.call_tool(
            "read_texpression", {"filepath": str(path), "seq_num": 0}
        )
        assert invalid_read.isError

        io = LowLevelIO()
        try:
            io.open_existing_repository_read(str(path))
            io.open_existing_repository_append(str(path))
            non_utf8 = TExpressions(io).write_node(b"\xff", [])
        finally:
            io.close_repository()
        bad_label = await session.call_tool(
            "read_texpression", {"filepath": str(path), "seq_num": non_utf8}
        )
        assert bad_label.isError


async def exercise_text_round_trip(path):
    lines = (ROOT / "docs" / "admin" / "README.md").read_text(encoding="utf-8").splitlines()
    text_size = sum(len(line.encode("utf-8")) + 1 for line in lines)
    async with connected_session("stdio") as session:
        created = await session.call_tool("create_repository", {"filepath": str(path)})
        assert not created.isError
        roots = []
        for line in lines * 5:
            tree = {
                "label": "",
                "children": [{"label": word, "children": []} for word in line.split()],
            }
            result = await session.call_tool(
                "write_texpression", {"filepath": str(path), "tree_json": json.dumps(tree)}
            )
            assert not result.isError, text(result)
            match = re.search(r"Sequence Number: (\d+)", text(result))
            assert match
            roots.append(int(match.group(1)))
        assert path.stat().st_size < text_size * 5
        for line, root in zip(lines, roots):
            result = await session.call_tool(
                "read_texpression", {"filepath": str(path), "seq_num": root}
            )
            assert not result.isError, text(result)
            tree = json.loads(text(result))
            assert [child["label"] for child in tree["children"]] == line.split()


@pytest.mark.parametrize("transport", ["stdio", "sse"])
def test_texpression_server(transport, tmp_path):
    anyio.run(exercise_server, transport, tmp_path / "trees.spade")


def test_text_round_trip(tmp_path):
    anyio.run(exercise_text_round_trip, tmp_path / "text.spade")
