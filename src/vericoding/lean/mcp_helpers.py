"""Lean LSP MCP integration (lean-lsp-mcp) for collecting context.

This module is copied from your ~/vericoding repo so `spec_to_code.py`
can optionally start a persistent MCP session and query tools when
processing Lean files. It degrades gracefully if MCP or deps are missing.
"""

from __future__ import annotations

from pathlib import Path
from typing import Iterable
import shutil
import threading
import os
import time
import socket
import subprocess
from datetime import timedelta

from vericoding.utils.git_utils import get_repo_root

try:
    import anyio
    from anyio.from_thread import start_blocking_portal
    from anyio.abc import BlockingPortal
    from mcp.client.stdio import StdioServerParameters, stdio_client
    from mcp.client import streamable_http
    from mcp.client.session import ClientSession
except Exception:  # allow import even if deps missing
    anyio = None  # type: ignore
    start_blocking_portal = None  # type: ignore
    BlockingPortal = None  # type: ignore
    StdioServerParameters = None  # type: ignore
    stdio_client = None  # type: ignore
    streamable_http = None  # type: ignore
    ClientSession = None  # type: ignore

# Persistent client state
_portal: "BlockingPortal | None" = None
_portal_cm = None  # context manager owning the portal
_session: "ClientSession | None" = None
_client_cm = None
_errlog_file = None
_available_tools: set[str] = set()
_lock = threading.Lock()


def _log(msg: str) -> None:
    try:
        root = get_repo_root()
        logdir = os.path.join(str(root), "logs")
        os.makedirs(logdir, exist_ok=True)
        path = os.path.join(logdir, "lean_mcp.log")
        from datetime import datetime
        with open(path, "a", encoding="utf-8") as f:
            f.write(f"[{datetime.now().isoformat(timespec='seconds')}] {msg}\n")
    except Exception:
        pass


# Best-effort monkey patch to reduce noisy teardown errors in some MCP versions
try:
    import mcp.client.stdio as _stdio_mod  # type: ignore
    from contextlib import asynccontextmanager as _acm

    _orig_stdio_client = _stdio_mod.stdio_client

    @_acm
    async def _patched_stdio_client(*args, **kwargs):  # type: ignore
        cm = _orig_stdio_client(*args, **kwargs)
        try:
            async with cm as rv:
                yield rv
        except RuntimeError as e:
            if "exit cancel scope" in str(e):
                _log("MCP: suppressed stdio cancel-scope RuntimeError on __aexit__")
            else:
                raise

    _stdio_mod.stdio_client = _patched_stdio_client  # type: ignore
    _log("MCP: applied stdio_client monkey patch for teardown noise")
except Exception:
    pass


def _deps_available() -> bool:
    return all(x is not None for x in (
        anyio, start_blocking_portal, StdioServerParameters, stdio_client, ClientSession
    ))


def _content_to_text(content) -> str:
    parts: list[str] = []
    for item in content or []:
        t = getattr(item, "type", None)
        if t == "text":
            parts.append(getattr(item, "text", ""))
        elif t == "resource":
            uri = getattr(item, "uri", "")
            parts.append(f"[resource] {uri}")
        else:
            parts.append(str(item))
    return "\n".join([p for p in parts if p])


async def _start_session_async(init_timeout: int) -> bool:
    global _session, _client_cm, _available_tools, _errlog_file
    if not _deps_available():
        return False
    uvx_path = shutil.which("uvx") or "uvx"
    root = str(get_repo_root())
    env = {**os.environ, "LEAN_PROJECT_PATH": root}
    server = StdioServerParameters(
        command="lake",
        args=["env", uvx_path, "lean-lsp-mcp"],
        env=env,
        cwd=root,
    )
    _log("MCP: starting server via: lake env uvx lean-lsp-mcp")
    # Capture server stderr to a file for debugging
    errf = None
    try:
        logdir = os.path.join(root, "logs")
        os.makedirs(logdir, exist_ok=True)
        err_path = os.path.join(logdir, "lean_mcp.stderr.log")
        errf = open(err_path, "ab", buffering=0)
    except Exception:
        errf = None
    cm = stdio_client(server, errlog=errf if errf is not None else None)
    read, write = await cm.__aenter__()
    sess = ClientSession(read, write)
    with anyio.fail_after(init_timeout):
        await sess.initialize()
    _log("MCP: initialized session")
    tools = await sess.list_tools()
    names = set()
    for t in getattr(tools, "tools", []) or []:
        name = getattr(t, "name", None)
        if name:
            names.add(name)
    _log(f"MCP: tools available: {sorted(list(names))}")
    _session = sess
    _client_cm = cm
    _errlog_file = errf
    _available_tools = names
    return True


def _ensure_persistent_started() -> bool:
    global _portal, _portal_cm
    if not _deps_available():
        _log("MCP: deps missing; cannot start session")
        return False
    with _lock:
        if _portal is not None and _session is not None:
            return True
        _portal_cm = start_blocking_portal()
        _portal = _portal_cm.__enter__()
        init_timeout = int(os.getenv("MCP_INIT_TIMEOUT", "10"))
        try:
            return bool(_portal.call(_start_session_async, init_timeout))
        except Exception as e:
            _log(f"MCP: failed to start session: {e}")
            return False


async def _call_tool_async(name: str, args: dict, timeout_sec: int):
    assert _session is not None
    res = await _session.call_tool(name, args, read_timeout_seconds=timedelta(seconds=timeout_sec))
    return _content_to_text(getattr(res, "content", None))


def _call_tool(name: str, args: dict, timeout_sec: int) -> str:
    if not _ensure_persistent_started():
        _log("MCP: _call_tool aborted, session not started")
        return ""
    assert _portal is not None
    try:
        return _portal.call(_call_tool_async, name, args, timeout_sec)
    except Exception as e:
        _log(f"MCP: call_tool {name} error: {e}")
        return ""


def tools_available() -> list[str]:
    if not _ensure_persistent_started():
        return []
    return sorted(list(_available_tools))


def ensure_server_started() -> bool:
    ok = _ensure_persistent_started()
    _log(f"MCP: ensure_server_started -> {ok}")
    return ok


def close_server() -> None:
    global _portal, _portal_cm, _session, _client_cm, _available_tools, _errlog_file
    with _lock:
        if _portal is None:
            return
        try:
            if _client_cm is not None and _portal is not None:
                _portal.call(_client_cm.__aexit__, None, None, None)
        except Exception:
            pass
        try:
            if _portal_cm is not None:
                _portal_cm.__exit__(None, None, None)
        except Exception:
            pass
        _portal = None
        _portal_cm = None
        _session = None
        _client_cm = None
        _available_tools = set()
        try:
            if _errlog_file is not None:
                _errlog_file.close()
        except Exception:
            pass
        _errlog_file = None


# Optional: HTTP fallback (one-shot) if requested via env
async def _collect_context_http_once_async(file_path: str, lines: list[int]) -> str:
    if any(x is None for x in (anyio, streamable_http, ClientSession)):
        return ""
    root = str(get_repo_root())
    logs_dir = os.path.join(root, "logs")
    os.makedirs(logs_dir, exist_ok=True)
    err_path = os.path.join(logs_dir, "lean_mcp_http.stderr.log")
    uvx_path = shutil.which("uvx") or "uvx"
    host = "127.0.0.1"

    def _free_port() -> int:
        s = socket.socket()
        s.bind((host, 0))
        p = s.getsockname()[1]
        s.close()
        return p

    last_exc: Exception | None = None
    for _attempt in range(3):
        port = _free_port()
        cmd = [
            "lake", "env", uvx_path, "lean-lsp-mcp",
            "--transport", "streamable-http",
            "--host", host,
            "--port", str(port),
        ]
        with open(err_path, "ab", buffering=0) as errf:
            proc = subprocess.Popen(cmd, cwd=root, stdout=subprocess.DEVNULL, stderr=errf)  # type: ignore
            try:
                time.sleep(0.8)
                if proc.poll() is not None:
                    continue
                url = f"http://{host}:{port}/mcp"
                async with streamable_http.streamablehttp_client(url) as (read, write, _get_sid):
                    sess = ClientSession(read, write)
                    with anyio.fail_after(int(os.getenv("MCP_INIT_TIMEOUT", "10"))):
                        await sess.initialize()
                    tools = await sess.list_tools()
                    names = set()
                    for t in getattr(tools, "tools", []) or []:
                        n = getattr(t, "name", None)
                        if n:
                            names.add(n)
                    fpath = str(Path(file_path).resolve())
                    ctxs: list[str] = []
                    if "lean_diagnostic_messages" in names:
                        diag = await sess.call_tool("lean_diagnostic_messages", {"file_path": fpath}, read_timeout_seconds=timedelta(seconds=6))
                        txt = _content_to_text(getattr(diag, "content", None))
                        if txt:
                            ctxs.append("[diagnostics]\n" + txt)
                    return "\n\n".join(ctxs)
            except Exception as e:
                last_exc = e
            finally:
                try:
                    proc.terminate()
                except Exception:
                    pass
    _log(f"MCP: http fallback failed: {last_exc}")
    return ""
