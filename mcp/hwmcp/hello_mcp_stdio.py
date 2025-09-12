import asyncio
from mcp.server import Server
from mcp.types import TextContent
from mcp.server.stdio import stdio_server

server = Server("spade-hello")

async def hello(name: str = "world") -> list[TextContent]:
    return [TextContent(type="text", text=f"Hello, {name}!")]

server.register_tool(hello)

async def main() -> None:
    async with stdio_server() as (read, write):
        await server.run(read, write, initialization_options={})

if __name__ == "__main__":
    asyncio.run(main())


