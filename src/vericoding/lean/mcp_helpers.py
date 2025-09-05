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
import threading
import os
from datetime import timedelta
from vericoding.utils.git_utils import get_repo_root
import anyio
from anyio.from_thread import start_blocking_portal
from anyio.abc import BlockingPortal

from mcp.client.stdio import StdioServerParameters, stdio_client
from mcp.client.session import ClientSession

# Persistent client state
_portal: BlockingPortal | None = None
_session: ClientSession | None = None
_client_cm = None
_available_tools: set[str] = set()
_lock = threading.Lock()


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


async def _start_session_async(init_timeout: int) -> bool:
    global _session, _client_cm, _available_tools
    if shutil.which("lean-lsp-mcp"):
        server = StdioServerParameters(command="lean-lsp-mcp", cwd=str(get_repo_root()))
    else:
        server = StdioServerParameters(command="uvx", args=["lean-lsp-mcp"], cwd=str(get_repo_root()))
    cm = stdio_client(server)
    read, write = await cm.__aenter__()
    sess = ClientSession(read, write)
    with anyio.fail_after(init_timeout):
        await sess.initialize()
    tools = await sess.list_tools()
    names = set()
    for t in getattr(tools, "tools", []) or []:
        name = getattr(t, "name", None)
        if name:
            names.add(name)
    _session = sess
    _client_cm = cm
    _available_tools = names
    return True


def _ensure_persistent_started() -> bool:
    global _portal
    with _lock:
        if _portal is not None and _session is not None:
            return True
        _portal = start_blocking_portal()
        init_timeout = int(os.getenv("MCP_INIT_TIMEOUT", "10"))
        try:
            return bool(_portal.call(_start_session_async, init_timeout))
        except Exception:
            return False


async def _call_tool_async(name: str, args: dict, timeout_sec: int):
    assert _session is not None
    res = await _session.call_tool(name, args, read_timeout_seconds=timedelta(seconds=timeout_sec))
    return _content_to_text(getattr(res, "content", None))


def _call_tool(name: str, args: dict, timeout_sec: int) -> str:
    if not _ensure_persistent_started():
        return ""
    assert _portal is not None
    try:
        return _portal.call(_call_tool_async, name, args, timeout_sec)
    except Exception:
        return ""


def _tools() -> set[str]:
    if not _ensure_persistent_started():
        return set()
    return set(_available_tools)


def _collect_context_persistent(file_path: str, lines: list[int]) -> str:
    tool_timeout = int(os.getenv("MCP_TOOL_TIMEOUT", "6"))
    fpath = str(Path(file_path).resolve())
    ctxs: list[str] = []
    avail = _tools()
    if "lean_diagnostic_messages" in avail:
        txt = _call_tool("lean_diagnostic_messages", {"file_path": fpath}, tool_timeout)
        if txt:
            ctxs.append("[diagnostics]\n" + txt)
    for ln in lines:
        if "lean_goal" in avail:
            txt = _call_tool("lean_goal", {"file_path": fpath, "line": int(ln), "column": 1}, tool_timeout)
            if txt:
                ctxs.append(f"[line {ln}] goals\n{txt}")
        if "lean_hover_info" in avail:
            txt = _call_tool("lean_hover_info", {"file_path": fpath, "line": int(ln), "column": 1}, tool_timeout)
            if txt:
                ctxs.append(f"[line {ln}] hover\n{txt}")
        if "lean_state_search" in avail:
            txt = _call_tool("lean_state_search", {"file_path": fpath, "line": int(ln), "column": 1}, tool_timeout)
            if txt:
                ctxs.append(f"[line {ln}] state_search\n{txt}")
        if "lean_hammer_premise" in avail:
            txt = _call_tool("lean_hammer_premise", {"file_path": fpath, "line": int(ln), "column": 1}, tool_timeout)
            if txt:
                ctxs.append(f"[line {ln}] hammer\n{txt}")
        if "lean_loogle" in avail:
            txt = _call_tool("lean_loogle", {"file_path": fpath, "line": int(ln), "column": 1}, tool_timeout)
            if txt:
                ctxs.append(f"[line {ln}] loogle\n{txt}")
        if "lean_leansearch" in avail:
            txt = _call_tool("lean_leansearch", {"file_path": fpath, "line": int(ln), "column": 1}, tool_timeout)
            if txt:
                ctxs.append(f"[line {ln}] leansearch\n{txt}")
    return "\n\n".join(ctxs)


def ensure_server_started() -> bool:
    """Ensure a persistent MCP session is running."""
    return _ensure_persistent_started()


def close_server() -> None:
    """Close persistent MCP session and tear down portal."""
    global _portal, _session, _client_cm, _available_tools
    with _lock:
        if _portal is None:
            return
        try:
            if _client_cm is not None:
                _portal.call(_client_cm.__aexit__, None, None, None)
        except Exception:
            pass
        try:
            _portal.close()
        except Exception:
            pass
        _portal = None
        _session = None
        _client_cm = None
        _available_tools = set()


def collect_lsp_context(file_path: str, lines: list[int]) -> str:
    return _collect_context_persistent(file_path, lines)


def collect_lsp_context_safe(file_path: str, lines: Iterable[int]) -> str:
    try:
        return collect_lsp_context(file_path, list(lines))
    except Exception:
        return ""
