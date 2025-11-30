import subprocess
import sys
import os
import time
import json
import shutil
import tempfile

def run_integration_test():
    print("Starting Integration Test...")
    
    # Setup temp dir for repo
    temp_dir = tempfile.mkdtemp()
    repo_path = os.path.join(temp_dir, "integration_test.spade")
    print(f"Using temporary repo path: {repo_path}")

    # Path to server script
    server_script = os.path.join(os.path.dirname(__file__), "../mcp/spade-mcp/src/spade_server.py")
    
    # We need to run the server as a subprocess.
    # FastMCP uses stdio by default for communication.
    # We will simulate a client by sending JSON-RPC messages to stdin.
    
    # Ensure PYTHONPATH includes workspace root so server can find 'kr'
    env = os.environ.copy()
    workspace_root = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
    env["PYTHONPATH"] = workspace_root + os.pathsep + env.get("PYTHONPATH", "")

    process = subprocess.Popen(
        [sys.executable, server_script],
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=sys.stderr,
        env=env,
        text=True,
        bufsize=0 # Unbuffered
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
        
        send_request("notifications/initialized", {}, None) # Notification, no ID

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
        import re
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

        print("SUCCESS: All integration steps passed.")

    except Exception as e:
        print(f"FAILED: {e}")
        raise
    finally:
        process.terminate()
        shutil.rmtree(temp_dir)

if __name__ == "__main__":
    run_integration_test()
