"""
Lean MCP client wrapper.

This module provides a light, best-effort interface to the `lean-lsp-mcp`
server via the Python `mcp` client library. It is intentionally resilient:
if the server or tools are unavailable, functions return empty strings
instead of raising, so the harness can fall back to plain `lean` verification.

Notes:
- Requires the `mcp` package and the `lean-lsp-mcp` server to be installed.
- We invoke the server using `uvx lean-lsp-mcp` to match project tooling.
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, List, Optional

import anyio

try:
    # Optional dependency; code must degrade gracefully if absent
    from mcp.client.session import ClientSession
    from mcp.client.stdio import StdioServerParameters, stdio_client
    MCP_AVAILABLE = True
except Exception:  # pragma: no cover - import guard
    MCP_AVAILABLE = False


DEFAULT_SERVER_CMD = "uvx"
DEFAULT_SERVER_ARGS = ["lean-lsp-mcp"]


@dataclass
class LeanMCPContext:
    diagnostics: str = ""
    term_goals: List[str] = None  # one per sorry line (best-effort)
    hovers: List[str] = None      # optional hovers for nearby symbols

    def render(self, max_len: int = 4000) -> str:
        parts: List[str] = []
        if self.diagnostics:
            parts.append("[Diagnostics]\n" + self.diagnostics.strip())
        if self.term_goals:
            tg = "\n\n".join(x.strip() for x in self.term_goals if x.strip())
            if tg:
                parts.append("[Term Goals]\n" + tg)
        if self.hovers:
            hv = "\n\n".join(x.strip() for x in self.hovers if x.strip())
            if hv:
                parts.append("[Hover]\n" + hv)
        text = "\n\n".join(parts).strip()
        if len(text) > max_len:
            return text[: max_len - 200] + "\n\n…(truncated)…"
        return text


async def _with_session(workdir: Path, fn):
    """Start a stdio MCP session and run fn(session)."""
    server = StdioServerParameters(command=DEFAULT_SERVER_CMD, args=DEFAULT_SERVER_ARGS, cwd=str(workdir))
    async with stdio_client(server) as (read_stream, write_stream):
        session = ClientSession(read_stream, write_stream)
        await session.initialize()
        return await fn(session)


def _collect_sorry_lines(code: str, limit: int = 5) -> List[int]:
    lines: List[int] = []
    for i, line in enumerate(code.splitlines(), start=1):
        if "sorry" in line:
            lines.append(i)
            if len(lines) >= limit:
                break
    return lines


def call_tool(workdir: Path, name: str, arguments: Optional[Dict[str, Any]] = None) -> str:
    """Call an MCP tool by name and return concatenated text contents.

    Returns empty string on any failure.
    """
    if not MCP_AVAILABLE:
        return ""

    async def _run(session: ClientSession) -> str:
        try:
            result = await session.call_tool(name, arguments or {})
            texts: List[str] = []
            for item in result.content or []:
                # TextContent has attribute 'text'
                text = getattr(item, "text", None)
                if text:
                    texts.append(text)
            return "\n".join(texts).strip()
        except Exception:
            return ""

    try:
        return anyio.run(_with_session, workdir, _run)
    except Exception:
        return ""


def collect_context(workdir: Path, file_path: Path, current_code: str) -> LeanMCPContext:
    """Best-effort harvest of diagnostics, term goals near `sorry`, and a few hovers."""
    ctx = LeanMCPContext(diagnostics="", term_goals=[], hovers=[])
    if not MCP_AVAILABLE:
        return ctx

    # Diagnostics for the full file
    diag = call_tool(workdir, "lean_diagnostic_messages", {"file_path": str(file_path)})
    ctx.diagnostics = diag or ""

    # Term goals at a few 'sorry' lines
    for ln in _collect_sorry_lines(current_code, limit=5):
        goal = call_tool(workdir, "lean_term_goal", {"file_path": str(file_path), "line": ln})
        if goal:
            ctx.term_goals.append(f"line {ln}:\n{goal}")

    # Simple hover info for the first few definitions (greedy heuristic)
    for i, line in enumerate(current_code.splitlines(), start=1):
        stripped = line.strip()
        if stripped.startswith("def ") or stripped.startswith("theorem ") or stripped.startswith("lemma "):
            hv = call_tool(workdir, "lean_hover_info", {"file_path": str(file_path), "line": i})
            if hv:
                ctx.hovers.append(f"line {i}:\n{hv}")
            if len(ctx.hovers) >= 3:
                break

    return ctx

