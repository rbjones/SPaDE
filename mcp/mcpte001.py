import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

import anyio
from mcp.client.sse import sse_client
from mcp.client.session import ClientSession
import anyio


HOST = os.getenv("SPADE_MCP_TEST_HOST", "127.0.0.1")
PORT = int(os.getenv("SPADE_MCP_TEST_PORT", "8765"))
SSE_URL = f"http://{HOST}:{PORT}/sse"
SERVER_SCRIPT = Path(__file__).with_name("mcpcd001.py")


def _first_text(result: object) -> str:
    content = getattr(result, "content", None)
    if not content:
        return ""
    for item in content:
        text_val = getattr(item, "text", None)
        if text_val is not None:
            return text_val
    return ""


def _start_server() -> subprocess.Popen:
    env = os.environ.copy()
    workspace_root = SERVER_SCRIPT.parent.parent.resolve()
    env["PYTHONPATH"] = str(workspace_root) + os.pathsep + env.get("PYTHONPATH", "")

    return subprocess.Popen(
        [
            sys.executable,
            str(SERVER_SCRIPT),
            "--transport",
            "sse",
            "--host",
            HOST,
            "--port",
            str(PORT),
        ],
        cwd=SERVER_SCRIPT.parent,
        stdout=subprocess.DEVNULL,  # avoid filling pipes if uvicorn logs verbosely
        stderr=subprocess.DEVNULL,
        text=True,
    )


async def _exercise_session(repo_path: str):
    async with sse_client(SSE_URL, timeout=5, sse_read_timeout=60) as (read_stream, write_stream):
        session = ClientSession(read_stream, write_stream)
        with anyio.fail_after(10):
            await session.initialize()

        with anyio.fail_after(10):
            tools_result = await session.list_tools()
        tool_names = [tool.name for tool in getattr(tools_result, "tools", [])]
        if "create_repository" not in tool_names:
            raise AssertionError("create_repository tool missing")

        with anyio.fail_after(10):
            create_result = await session.call_tool("create_repository", {"filepath": repo_path})
        create_text = _first_text(create_result)
        print(f"<- Create Repo: {create_text}")

        if not os.path.exists(repo_path):
            raise AssertionError("Repository file was not created")

        with anyio.fail_after(10):
            write_result = await session.call_tool(
                "write_sexpression",
                {"filepath": repo_path, "sexp_json": '["Hello", "World"]'},
            )
        write_text = _first_text(write_result)
        print(f"<- Write S-Exp: {write_text}")

        match = re.search(r"Sequence Number: (\d+)", write_text)
        if not match:
            raise AssertionError("Could not parse sequence number from response")
        seq_num = int(match.group(1))

        with anyio.fail_after(10):
            read_result = await session.call_tool(
                "read_sexpression",
                {"filepath": repo_path, "seq_num": seq_num},
            )
        read_text = _first_text(read_result)
        print(f"<- Read S-Exp: {read_text}")

        expected = json.loads('["Hello", ["World", null]]')
        if json.loads(read_text) != expected:
            raise AssertionError(f"Read mismatch! Expected {expected}, got {read_text}")


async def _connect_with_retry(repo_path: str, retries: int = 12, delay: float = 0.5):
    last_error: Exception | None = None
    for _ in range(retries):
        try:
            await _exercise_session(repo_path)
            return
        except Exception as exc:  # noqa: PERF203 - we want the last error
            last_error = exc
            await anyio.sleep(delay)
    raise last_error if last_error else RuntimeError("Failed to connect to SSE server")


def test_integration():
    print("Starting Integration Test (SSE)...")

    temp_dir = tempfile.mkdtemp()
    repo_path = os.path.join(temp_dir, "integration_test.spade")

    server_process = _start_server()

    try:
        anyio.run(_connect_with_retry, repo_path)
        print("SUCCESS: All integration steps passed.")
    finally:
        server_process.terminate()
        try:
            server_process.wait(timeout=5)
        except Exception:
            server_process.kill()
        try:
            server_process.wait(timeout=5)
        except Exception:
            server_process.kill()
        if server_process.stdout:
            _ = server_process.stdout.read()
        shutil.rmtree(temp_dir)


if __name__ == "__main__":
    test_integration()
