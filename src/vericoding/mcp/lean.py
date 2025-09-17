"""Lean MCP integration utilities."""

from __future__ import annotations

import asyncio
import json
import threading
from typing import Any, Dict, Iterable, List, Optional

import mcp.types as mcp_types
from mcp.client.session import ClientSession
from mcp.client.stdio import StdioServerParameters, stdio_client


class LeanMCPManager:
    """Manage a long-lived connection to the ``lean-lsp-mcp`` server."""

    def __init__(
        self,
        *,
        command: str = "uvx",
        args: Optional[List[str]] = None,
        env: Optional[Dict[str, str]] = None,
        cwd: Optional[str] = None,
        startup_timeout: float = 30.0,
    ) -> None:
        self._command = command
        self._args = args or ["lean-lsp-mcp", "--transport", "stdio"]
        self._env = env
        self._cwd = cwd
        self._startup_timeout = startup_timeout

        self._loop: asyncio.AbstractEventLoop | None = None
        self._thread: threading.Thread | None = None
        self._stop_future: asyncio.Future[None] | None = None
        self._session: ClientSession | None = None

        self._tools: List[mcp_types.Tool] = []
        self._instructions: str | None = None
        self._tool_lock = threading.Lock()

        self._ready = threading.Event()
        self._startup_error: BaseException | None = None

    # ------------------------------------------------------------------
    # Lifecycle management
    # ------------------------------------------------------------------
    def start(self) -> None:
        """Start the background MCP server connection."""

        if self._thread and self._thread.is_alive():
            return

        self._ready.clear()
        self._thread = threading.Thread(
            target=self._thread_main,
            name="LeanMCPThread",
            daemon=True,
        )
        self._thread.start()

        if not self._ready.wait(timeout=self._startup_timeout):
            self._startup_error = TimeoutError(
                "Timed out waiting for lean-lsp-mcp to start"
            )

        if self._startup_error is not None:
            raise RuntimeError(
                "Failed to start lean-lsp-mcp"
            ) from self._startup_error

    def close(self) -> None:
        """Stop the background loop and terminate the MCP session."""

        if self._loop and self._stop_future and not self._stop_future.done():
            self._loop.call_soon_threadsafe(self._stop_future.set_result, None)

        if self._thread and self._thread.is_alive():
            self._thread.join(timeout=5)

    # ------------------------------------------------------------------
    # Public helpers
    # ------------------------------------------------------------------
    @property
    def instructions(self) -> str | None:
        """Instructions provided by the MCP server."""

        return self._instructions

    def openai_tools(self) -> List[Dict[str, Any]]:
        """Return the tool definitions in OpenAI-compatible schema."""

        self.ensure_started()

        with self._tool_lock:
            tools_snapshot = list(self._tools)

        openai_tools: List[Dict[str, Any]] = []
        for tool in tools_snapshot:
            parameters = tool.inputSchema or {"type": "object", "properties": {}}
            openai_tools.append(
                {
                    "type": "function",
                    "function": {
                        "name": tool.name,
                        "description": tool.description or "",
                        "parameters": parameters,
                    },
                }
            )
        return openai_tools

    def ensure_started(self) -> None:
        """Ensure the MCP session is active."""

        if not self._thread or not self._thread.is_alive():
            self.start()

    def call_tool(self, name: str, arguments: Dict[str, Any] | None = None) -> str:
        """Invoke a Lean MCP tool and return its textual output."""

        self.ensure_started()
        if self._loop is None or self._session is None:
            raise RuntimeError("Lean MCP session is not initialized")

        async def _invoke() -> str:
            call_result = await self._session.call_tool(name, arguments or {})
            return self._format_tool_content(call_result.content)

        future = asyncio.run_coroutine_threadsafe(_invoke(), self._loop)
        return future.result()

    # ------------------------------------------------------------------
    # Internal methods
    # ------------------------------------------------------------------
    def _thread_main(self) -> None:
        self._loop = asyncio.new_event_loop()
        asyncio.set_event_loop(self._loop)
        self._stop_future = self._loop.create_future()

        try:
            self._loop.run_until_complete(self._run_session())
        except BaseException as exc:  # pylint: disable=broad-except
            self._startup_error = exc
            self._ready.set()
        finally:
            if self._loop is not None and not self._loop.is_closed():
                self._loop.run_until_complete(self._loop.shutdown_asyncgens())
                self._loop.close()

    async def _run_session(self) -> None:
        params = StdioServerParameters(
            command=self._command,
            args=self._args,
            env=self._env,
            cwd=self._cwd,
        )

        try:
            async with stdio_client(params) as (read_stream, write_stream):
                self._session = ClientSession(
                    read_stream,
                    write_stream,
                    message_handler=self._handle_message,
                )
                init_result = await self._session.initialize()
                self._instructions = init_result.instructions
                await self._refresh_tools()
                self._ready.set()

                if self._stop_future is not None:
                    await self._stop_future
        finally:
            self._session = None
            if not self._ready.is_set():
                self._ready.set()

    async def _refresh_tools(self) -> None:
        if self._session is None:
            return
        tools_result = await self._session.list_tools()
        with self._tool_lock:
            self._tools = list(tools_result.tools)

    async def _handle_message(self, message: Any) -> None:  # noqa: ANN401
        if isinstance(message, mcp_types.ServerNotification):
            root = message.root
            if isinstance(root, mcp_types.ToolListChangedNotification):
                await self._refresh_tools()
        elif isinstance(message, Exception):
            self._startup_error = message

    @staticmethod
    def _format_tool_content(content: Iterable[Any]) -> str:
        parts: List[str] = []
        for item in content:
            item_type = getattr(item, "type", None)
            if item_type == "text":
                text = getattr(item, "text", "")
                if text:
                    parts.append(text)
            else:
                try:
                    parts.append(json.dumps(item.model_dump(), ensure_ascii=False))
                except AttributeError:
                    parts.append(str(item))
        return "\n".join(part for part in parts if part)


__all__ = ["LeanMCPManager"]
