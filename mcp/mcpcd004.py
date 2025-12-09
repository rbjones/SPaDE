"""Abstract contracts derived by reverse-engineering the MCP helpers in this directory.

These ABCs capture the behaviour of the prototypes in `mcpcd001.py`, `mcpcd002.py`,
and the integration driver `mcpte001.py` so that future work can be documented and
extended without rewriting the runtime logic every time.
"""

from __future__ import annotations

import abc
from typing import Any


class SpadeRepoServerABC(abc.ABC):
    """Defines the toolset exported by the SPaDE repository FastMCP server."""

    @abc.abstractmethod
    async def create_repository(self, filepath: str, version: int = 1) -> str:
        """Create a write-once repository file whose header records ``version``.

        The prototype opens a new repository via :class:`kr.krcd009.LowLevelIO`,
        writes the version as an NTBS integer, and closes the file. On success
        it raises no exceptions and returns a friendly confirmation message.
        Any failure should raise or return an descriptive error string.
        """

    @abc.abstractmethod
    async def write_sexpression(self, filepath: str, sexp_json: str) -> str:
        """Append a JSON-encoded S-expression to the existing repository.

        The payload is parsed with :mod:`json`, converted to bytes recursively,
        and then written via a read-then-append workflow so optimistic locking
        detects concurrent writers. ``StaleCacheError`` should be handled with
        a retry-friendly message.
        """

    @abc.abstractmethod
    async def read_sexpression(self, filepath: str, seq_num: int) -> str:
        """Read a sequence number from the repository and return JSON text.

        The implementation converts repository bytes back to Python objects,
        maps tuples to nested lists, and serializes the result to JSON so callers
        can ingest the structure without needing to understand the storage
        encoding.
        """


class MinimalMCPServerABC(abc.ABC):
    """Describes the trivial FastMCP server used only for smoke-testing."""

    @abc.abstractmethod
    async def ping(self) -> str:
        """Return ``'pong'`` to prove the server can respond to synchronous
        requests without side effects."""


class MCPIntegrationTestABC(abc.ABC):
    """Contract for the subprocess-based integration test harness.

    The real script launches ``mcpcd001.py`` in a subprocess, speaks the
    FastMCP JSON-RPC protocol over its STDIN/STDOUT streams, and validates
    that repository creation, write, and read tools behave correctly.
    """

    @abc.abstractmethod
    def run_full_cycle(self) -> None:
        """Execute the full sequence: initialize, list tools, create repo,
        write an S-expression, read it back, and tear down.

        Implementations should document the server handshake and cleanup
        semantics so the steps are reproducible when the harness is extended.
        """

    @abc.abstractmethod
    def send_tool_call(self, method: str, params: dict[str, Any], request_id: int | None) -> None:
        """Serialize a JSON-RPC ``tools/call`` message and write it to the
        subprocess STDIN, flushing immediately to avoid buffering traps."""

    @abc.abstractmethod
    def read_tool_response(self) -> Any:
        """Read a single line from the subprocess STDOUT and parse the
        JSON-RPC response, raising if the server closes the stream unexpectedly."""
