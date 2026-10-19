import os
import json
import re
import socket
import shutil
import subprocess
import sys
import tempfile
import time

import anyio
from mcp.client.session import ClientSession
from mcp.client.sse import sse_client


SSE_HOST = os.getenv("SPADE_MCP_TEST_HOST", "127.0.0.1")
SSE_PORT = int(os.getenv("SPADE_MCP_TEST_PORT", "8765"))
SERVER_SCRIPT = os.path.join(os.path.dirname(__file__), "mcpcd001.py")


def test_integration():
    print("Starting Integration Test...")

    # Setup temp dir for repo
    temp_dir = tempfile.mkdtemp()
    repo_path = os.path.join(temp_dir, "integration_test.spade")
    print(f"Using temporary repo path: {repo_path}")

    # Path to server script
    # Adjusted for location: mcp/mcpte001.py -> mcp/mcpcd001.py
    server_script = SERVER_SCRIPT

    # We need to run the server as a subprocess.
    # FastMCP uses stdio by default for communication.
    # We will simulate a client by sending JSON-RPC messages to stdin.

    # Ensure PYTHONPATH includes workspace root so server can find 'kr'
    env = os.environ.copy()
    # Adjusted for location: mcp/mcpte001.py -> workspace root is ../
    workspace_root = os.path.abspath(os.path.join(os.path.dirname(__file__), "../"))
    env["PYTHONPATH"] = workspace_root + os.pathsep + env.get("PYTHONPATH", "")

    process = subprocess.Popen(
        [sys.executable, server_script],
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=sys.stderr,
        env=env,
        text=True,
        bufsize=0  # Unbuffered
    )

    def send_request(method, params, req_id):
        req = {
            "jsonrpc": "2.0",
            "method": method,
            "params": params,
            "id": req_id
        }
        json_str = json.dumps(req)
        print(f"-> Sending: {method}")
        process.stdin.write(json_str + "\n")
        process.stdin.flush()

    def read_response():
        line = process.stdout.readline()
        if not line:
            raise Exception("Server closed connection unexpectedly")
        return json.loads(line)

    try:
        # 1. Initialize (MCP handshake)
        # FastMCP might expect 'initialize' first.
        send_request("initialize", {
            "protocolVersion": "2024-11-05",
            "capabilities": {},
            "clientInfo": {"name": "test-client", "version": "1.0"}
        }, 1)

        resp = read_response()
        print(f"<- Init Response: {resp.get('result', {}).get('serverInfo', {}).get('name')}")

        send_request("notifications/initialized", {}, None)  # Notification, no ID

        # 2. List Tools (Verify our tools are present)
        send_request("tools/list", {}, 2)
        resp = read_response()
        tools = [t['name'] for t in resp['result']['tools']]
        print(f"<- Tools available: {tools}")
        if "create_repository" not in tools:
            raise Exception("create_repository tool missing!")

        # 3. Create Repository
        send_request("tools/call", {
            "name": "create_repository",
            "arguments": {"filepath": repo_path}
        }, 3)
        resp = read_response()
        print(f"<- Create Repo: {resp['result']['content'][0]['text']}")

        if not os.path.exists(repo_path):
            raise Exception("Repository file was not created!")

        # 4. Write S-Expression
        # Write ["Hello", "World"] -> (Hello . (World . Nil))
        sexp_data = '["Hello", "World"]'
        send_request("tools/call", {
            "name": "write_sexpression",
            "arguments": {"filepath": repo_path, "sexp_json": sexp_data}
        }, 4)
        resp = read_response()
        content = resp['result']['content'][0]['text']
        print(f"<- Write S-Exp: {content}")

        # Extract seq_num from response string "Successfully wrote ... Sequence Number: X"
        match = re.search(r"Sequence Number: (\d+)", content)
        if not match:
            raise Exception("Could not parse sequence number from response")
        seq_num = int(match.group(1))

        # 5. Read S-Expression
        send_request("tools/call", {
            "name": "read_sexpression",
            "arguments": {"filepath": repo_path, "seq_num": seq_num}
        }, 5)
        resp = read_response()
        read_json = resp['result']['content'][0]['text']
        print(f"<- Read S-Exp: {read_json}")

        # Verify content
        # read_recursive returns tuples for Cons: (Hello, (World, None))
        # Our server converts tuples to lists for JSON: ["Hello", ["World", None]]
        expected = '["Hello", ["World", null]]'
        if json.loads(read_json) != json.loads(expected):
            raise Exception(f"Read mismatch! Expected {expected}, got {read_json}")

        print("Basic read/write steps passed.")

        # 6. Round-trip text through the server, one S-expression (list of
        # words) per line, then compare content and size.
        req_ids = iter(range(10, 10**9))

        def flatten(cons):
            # Nested [car, cdr] pairs ending in null -> flat list of words
            out = []
            while cons is not None:
                out.append(cons[0])
                cons = cons[1]
            return out

        def call_tool(name, arguments):
            send_request("tools/call", {"name": name, "arguments": arguments}, next(req_ids))
            return read_response()['result']['content'][0]['text']

        def round_trip(lines, repo_file):
            words_by_line = [line.split() for line in lines]
            call_tool("create_repository", {"filepath": repo_file})
            seq_nums = []
            for words in words_by_line:
                content = call_tool("write_sexpression",
                                    {"filepath": repo_file, "sexp_json": json.dumps(words)})
                match = re.search(r"Sequence Number: (\d+)", content)
                if not match:
                    raise Exception(f"Write failed: {content}")
                seq_nums.append(int(match.group(1)))
            for i, (seq, words) in enumerate(zip(seq_nums, words_by_line)):
                text = call_tool("read_sexpression", {"filepath": repo_file, "seq_num": seq})
                if flatten(json.loads(text)) != words:
                    raise Exception(f"Line {i + 1} mismatch: expected {words}, got {text}")
            return os.path.getsize(repo_file)

        text_path = os.path.join(os.path.dirname(__file__), "..", "docs", "admin", "README.md")
        with open(text_path, encoding="utf-8") as f:
            lines = f.read().splitlines()
        text_size = sum(len(line.encode("utf-8")) + 1 for line in lines)
        repo_size = round_trip(lines, os.path.join(temp_dir, "words.spade"))
        print(f"Round-trip OK: {len(lines)} lines, "
              f"{sum(len(line.split()) for line in lines)} words")
        # Each distinct atom/cons is stored once, but ordinary prose has few
        # repeated cons cells, so the repo is typically larger than the text.
        print(f"File size: {text_size} bytes, repo size: {repo_size} bytes "
              f"(ratio {repo_size / text_size:.2f})")

        # Repeated content is shared, so the repo must be smaller than the text.
        copies = 5
        rep_lines = lines * copies
        rep_text_size = text_size * copies
        rep_repo_size = round_trip(rep_lines, os.path.join(temp_dir, "repeated.spade"))
        print(f"Repeated x{copies}: file size {rep_text_size} bytes, "
              f"repo size {rep_repo_size} bytes")
        if rep_repo_size >= rep_text_size:
            raise Exception("Repository is not smaller than the repeated source text!")

        print("SUCCESS: All integration steps passed.")

    except Exception as e:
        print(f"FAILED: {e}")
        raise
    finally:
        process.terminate()
        shutil.rmtree(temp_dir)


def _start_sse_server(use_cli_options):
    env = os.environ.copy()
    workspace_root = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
    env["PYTHONPATH"] = workspace_root + os.pathsep + env.get("PYTHONPATH", "")
    env["SPADE_MCP_HOST"] = SSE_HOST
    command = [sys.executable, SERVER_SCRIPT]
    if use_cli_options:
        env["SPADE_MCP_TRANSPORT"] = "stdio"
        env["SPADE_MCP_PORT"] = "1"
        command.extend(
            [
                "--transport",
                "sse",
                "--host",
                SSE_HOST,
                "--port",
                str(SSE_PORT),
            ]
        )
    else:
        env["SPADE_MCP_TRANSPORT"] = "sse"
        env["SPADE_MCP_PORT"] = str(SSE_PORT)
    return subprocess.Popen(
        command,
        cwd=os.path.dirname(SERVER_SCRIPT),
        env=env,
        stdout=subprocess.DEVNULL,
        stderr=sys.stderr,
        text=True,
    )


def _wait_for_server(process):
    deadline = time.monotonic() + 10
    while time.monotonic() < deadline:
        if process.poll() is not None:
            raise RuntimeError(f"SSE server exited with status {process.returncode}")
        try:
            with socket.create_connection((SSE_HOST, SSE_PORT), timeout=0.2):
                return
        except OSError:
            time.sleep(0.1)
    raise TimeoutError(f"SSE server did not start on {SSE_HOST}:{SSE_PORT}")


async def _exercise_sse(repo_path):
    url = f"http://{SSE_HOST}:{SSE_PORT}/sse"
    async with sse_client(url, timeout=5, sse_read_timeout=60) as (read_stream, write_stream):
        async with ClientSession(read_stream, write_stream) as session:
            with anyio.fail_after(10):
                await session.initialize()
            with anyio.fail_after(10):
                tools_result = await session.list_tools()
            tool_names = [tool.name for tool in tools_result.tools]
            if "create_repository" not in tool_names:
                raise AssertionError("create_repository tool missing from SSE server")

            with anyio.fail_after(10):
                await session.call_tool("create_repository", {"filepath": repo_path})
            if not os.path.exists(repo_path):
                raise AssertionError("SSE server did not create the repository")

            with anyio.fail_after(10):
                write_result = await session.call_tool(
                    "write_sexpression",
                    {"filepath": repo_path, "sexp_json": '["Hello", "World"]'},
                )
            write_text = next(item.text for item in write_result.content if item.type == "text")
            match = re.search(r"Sequence Number: (\d+)", write_text)
            if not match:
                raise AssertionError(f"SSE write failed: {write_text}")

            with anyio.fail_after(10):
                read_result = await session.call_tool(
                    "read_sexpression",
                    {"filepath": repo_path, "seq_num": int(match.group(1))},
                )
            read_text = next(item.text for item in read_result.content if item.type == "text")
            expected = ["Hello", ["World", None]]
            if json.loads(read_text) != expected:
                raise AssertionError(f"SSE read mismatch: expected {expected}, got {read_text}")


def _run_sse_transport_test(use_cli_options):
    temp_dir = tempfile.mkdtemp()
    repo_path = os.path.join(temp_dir, "sse_integration_test.spade")
    server_process = _start_sse_server(use_cli_options)
    try:
        _wait_for_server(server_process)
        anyio.run(_exercise_sse, repo_path)
    finally:
        server_process.terminate()
        try:
            server_process.wait(timeout=5)
        except subprocess.TimeoutExpired:
            server_process.kill()
            server_process.wait(timeout=5)
        shutil.rmtree(temp_dir)


def test_sse_transport():
    _run_sse_transport_test(use_cli_options=False)
    _run_sse_transport_test(use_cli_options=True)


if __name__ == "__main__":
    test_integration()
