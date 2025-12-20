import argparse
import json
import os
import sys
import logging
import traceback

# Emergency logging to /tmp to catch early failures
try:
    with open("/tmp/spade_server_startup.log", "a") as f:
        f.write(f"Startup attempt at {os.popen('date').read()}")
        f.write(f"Executable: {sys.executable}\n")
        f.write(f"CWD: {os.getcwd()}\n")
        f.write(f"Path: {sys.path}\n")
except Exception:
    pass

# Setup logging to debug startup issues
log_file = os.path.join(os.path.dirname(os.path.abspath(__file__)), "server.log")
try:
    logging.basicConfig(
        filename=log_file,
        level=logging.DEBUG,
        format='%(asctime)s - %(levelname)s - %(message)s'
    )
    logging.info("Server starting...")
except Exception as e:
    with open("/tmp/spade_server_startup.log", "a") as f:
        f.write(f"Failed to setup logging: {e}\n")


def _as_int(value: str | int | None, fallback: int) -> int:
    """Parse an int with a safe fallback."""
    try:
        return int(value)  # type: ignore[arg-type]
    except Exception:
        return fallback

try:
    from mcp.server.fastmcp import FastMCP

    # Defaults can be overridden by CLI flags or env vars.
    DEFAULT_TRANSPORT = os.getenv("SPADE_MCP_TRANSPORT", "sse")
    DEFAULT_HOST = os.getenv("SPADE_MCP_HOST", "127.0.0.1")
    DEFAULT_PORT = _as_int(os.getenv("SPADE_MCP_PORT", "8000"), 8000)
    DEFAULT_MOUNT_PATH = os.getenv("SPADE_MCP_MOUNT_PATH")
    DEFAULT_SSE_PATH = os.getenv("SPADE_MCP_SSE_PATH")

    # Import our SPaDE repo library
    # Note: We need to ensure 'kr' is in the python path.
    # For this prototype, we will assume the server is run from the workspace root
    # or we will adjust sys.path.

    # Add the workspace root to sys.path to allow importing 'kr'
    current_dir = os.path.dirname(os.path.abspath(__file__))
    workspace_root = os.path.abspath(os.path.join(current_dir, "../"))
    logging.info(f"Current dir: {current_dir}")
    logging.info(f"Workspace root calculated as: {workspace_root}")

    if workspace_root not in sys.path:
        sys.path.append(workspace_root)
        logging.info(f"Added {workspace_root} to sys.path")

    logging.info(f"sys.path: {sys.path}")

    try:
        from kr.krcd009 import LowLevelIO, SExpressions, StaleCacheError
        logging.info("Successfully imported kr.krcd009")
    except ImportError as e:
        logging.error(f"Failed to import kr.krcd009: {e}")
        raise
    except Exception as e:
        logging.error(f"Unexpected error during import: {e}")
        raise

    # Initialize FastMCP server
    server = FastMCP("SPaDE-server", host=DEFAULT_HOST, port=DEFAULT_PORT)

    @server.tool()
    async def create_repository(filepath: str, version: int = 1) -> str:
        """
        Creates a new SPaDE repository at the specified filepath.

        Args:
            filepath: Absolute path to the new repository file.
            version: Version number for the repository (default 1).
        """
        try:
            io = LowLevelIO()
            io.open_new_repository(filepath, version=version)
            io.close_repository()
            return f"Successfully created repository at {filepath} with version {version}"
        except Exception as e:
            return f"Error creating repository: {str(e)}"

    @server.tool()
    async def write_sexpression(filepath: str, sexp_json: str) -> str:
        """
        Writes an S-expression to an existing SPaDE repository.

        Args:
            filepath: Absolute path to the repository file.
            sexp_json: JSON string representing the S-expression.
                       - Strings are converted to Atoms (bytes).
                       - Lists are converted to Cons chains.
                       - Null/None is converted to Nil.
                       Example: '["A", "B"]' -> (A . (B . Nil))
        """
        try:
            # Parse JSON input
            data = json.loads(sexp_json)

            # Convert strings to bytes for the repo library
            def to_bytes_recursive(obj):
                if isinstance(obj, str):
                    return obj.encode('utf-8')
                elif isinstance(obj, list):
                    return [to_bytes_recursive(x) for x in obj]
                elif obj is None:
                    return None
                else:
                    return obj  # Let write_recursive handle error or other types

            data_bytes = to_bytes_recursive(data)

            io = LowLevelIO()
            # Open read first to cache
            io.open_existing_repository_read(filepath)
            # Then open append
            io.open_existing_repository_append(filepath)

            sexp = SExpressions(io)
            seq_num = sexp.write_recursive(data_bytes)

            io.close_repository()
            return f"Successfully wrote S-expression. Sequence Number: {seq_num}"
        except StaleCacheError:
            return "Error: Repository was modified by another process. Please retry."
        except Exception as e:
            return f"Error writing S-expression: {str(e)}"

    @server.tool()
    async def read_sexpression(filepath: str, seq_num: int) -> str:
        """
        Reads an S-expression from a SPaDE repository by sequence number.

        Args:
            filepath: Absolute path to the repository file.
            seq_num: The sequence number to read.
        """
        try:
            io = LowLevelIO()
            io.open_existing_repository_read(filepath)

            sexp = SExpressions(io)
            val = sexp.read_recursive(seq_num)

            io.close_repository()

            # Convert bytes back to strings for JSON output
            def from_bytes_recursive(obj):
                if isinstance(obj, bytes):
                    return obj.decode('utf-8')
                elif isinstance(obj, tuple):
                    return [from_bytes_recursive(x) for x in obj]
                elif obj is None:
                    return None
                else:
                    return str(obj)

            result = from_bytes_recursive(val)
            return json.dumps(result)
        except Exception as e:
            return f"Error reading S-expression: {str(e)}"

    def parse_args():
        parser = argparse.ArgumentParser(description="SPaDE MCP server")
        parser.add_argument(
            "--transport",
            choices=["stdio", "sse", "streamable-http"],
            default=DEFAULT_TRANSPORT,
            help="MCP transport to use (default: sse)",
        )
        parser.add_argument("--host", default=DEFAULT_HOST, help="Bind host for SSE/HTTP transport")
        parser.add_argument(
            "--port",
            type=int,
            default=DEFAULT_PORT,
            help="Bind port for SSE/HTTP transport",
        )
        parser.add_argument(
            "--mount-path",
            default=DEFAULT_MOUNT_PATH,
            help="Optional mount path prefix for the SSE app",
        )
        parser.add_argument(
            "--sse-path",
            default=DEFAULT_SSE_PATH,
            help="Override the SSE path (default /sse)",
        )
        return parser.parse_args()

    def configure_server(args):
        server.settings.host = args.host
        server.settings.port = args.port

        if args.mount_path:
            server.settings.mount_path = args.mount_path

        if args.sse_path:
            server.settings.sse_path = args.sse_path

        logging.info(
            "Launching MCP server transport=%s host=%s port=%s mount=%s sse_path=%s",
            args.transport,
            server.settings.host,
            server.settings.port,
            server.settings.mount_path,
            server.settings.sse_path,
        )

    if __name__ == "__main__":
        args = parse_args()
        configure_server(args)
        server.run(transport=args.transport, mount_path=args.mount_path)

except Exception as e:
    logging.critical(f"Fatal error: {e}")
    logging.critical(traceback.format_exc())
    with open("/tmp/spade_server_startup.log", "a") as f:
        f.write(f"Fatal error: {e}\n")
        f.write(traceback.format_exc())
    sys.exit(1)
