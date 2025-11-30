from mcp.server.fastmcp import FastMCP
import logging
import os

# Setup logging
log_file = os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../minimal_server.log")
logging.basicConfig(filename=log_file, level=logging.DEBUG)
logging.info("Minimal server starting...")

server = FastMCP("minimal-server")

@server.tool()
def ping() -> str:
    return "pong"

if __name__ == "__main__":
    server.run()
