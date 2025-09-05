"""Lean LSP MCP integration (lean-lsp-mcp) for collecting context.

We spawn the MCP server (`uvx lean-lsp-mcp`) via stdio and query tools:
- lean_diagnostic_messages
- lean_goal
- lean_hover_info
- (optionally) lean_leansearch / lean_loogle

This module provides synchronous helpers that launch the MCP server per call.
Keeping a persistent background client is possible but unnecessary for our
throughput; correctness first.
"""

from __future__ import annotations

from pathlib import Path
from typing import Iterable
import shutil
from datetime import timedelta
from vericoding.utils.git_utils import get_repo_root
import anyio

from mcp.client.stdio import StdioServerParameters, stdio_client
from mcp.client.session import ClientSession


def _content_to_text(content) -> str:
    parts: list[str] = []
    for item in content or []:
        t = getattr(item, "type", None)
        if t == "text":
            parts.append(getattr(item, "text", ""))
        elif t == "resource":
            # Show resource URI
            uri = getattr(item, "uri", "")
            parts.append(f"[resource] {uri}")
        else:
            # Fallback to string
            parts.append(str(item))
    return "\n".join([p for p in parts if p])


async def _collect_context_async(file_path: str, lines: list[int]) -> str:
    # Resolve timeouts via env or defaults
    import os
    init_timeout = int(os.getenv("MCP_INIT_TIMEOUT", "8"))
    tool_timeout = int(os.getenv("MCP_TOOL_TIMEOUT", "4"))

    # Prefer direct console script if installed; fallback to `uvx`
    if shutil.which("lean-lsp-mcp"):
        server = StdioServerParameters(command="lean-lsp-mcp", cwd=str(get_repo_root()))
    else:
        server = StdioServerParameters(command="uvx", args=["lean-lsp-mcp"], cwd=str(get_repo_root()))
    async with stdio_client(server) as (read, write):
        sess = ClientSession(read, write)
        # Initialize with timeout
        try:
            with anyio.fail_after(init_timeout):
                await sess.initialize()
        except Exception:
            return ""

        fpath = str(Path(file_path).resolve())
        ctxs: list[str] = []

        # Discover available tools to avoid hard-coding
        available = set()
        try:
            tools = await sess.list_tools()
            for t in getattr(tools, "tools", []) or []:
                name = getattr(t, "name", None)
                if name:
                    available.add(name)
        except Exception:
            pass

        # Diagnostics for the whole file
        try:
            if "lean_diagnostic_messages" in available:
                diag = await sess.call_tool(
                    "lean_diagnostic_messages",
                    {"file_path": fpath},
                    read_timeout_seconds=timedelta(seconds=tool_timeout),
                )
            else:
                diag = None
            text = _content_to_text(diag.content)
            if text:
                ctxs.append("[diagnostics]\n" + text)
        except Exception:
            pass

        for ln in lines:
            try:
                if "lean_goal" in available:
                    goal = await sess.call_tool(
                        "lean_goal",
                        {"file_path": fpath, "line": int(ln), "column": 1},
                        read_timeout_seconds=timedelta(seconds=tool_timeout),
                    )
                else:
                    goal = None
                goal_text = _content_to_text(goal.content)
                if goal_text:
                    ctxs.append(f"[line {ln}] goals\n{goal_text}")
            except Exception:
                pass
            try:
                if "lean_hover_info" in available:
                    hov = await sess.call_tool(
                        "lean_hover_info",
                        {"file_path": fpath, "line": int(ln), "column": 1},
                        read_timeout_seconds=timedelta(seconds=tool_timeout),
                    )
                else:
                    hov = None
                hov_text = _content_to_text(hov.content)
                if hov_text:
                    ctxs.append(f"[line {ln}] hover\n{hov_text}")
            except Exception:
                pass

        return "\n\n".join(ctxs)


def ensure_server_started() -> bool:
    """Compatibility shim (always returns True if uvx is present)."""
    # We don't keep a persistent server here; stdio_client handles lifecycle per call
    return True


def close_server() -> None:
    """No-op: server is per-call."""
    return None


def collect_lsp_context(file_path: str, lines: list[int]) -> str:
    return anyio.run(_collect_context_async, file_path, lines)


def collect_lsp_context_safe(file_path: str, lines: Iterable[int]) -> str:
    try:
        return collect_lsp_context(file_path, list(lines))
    except Exception:
        return ""
