"""Helpers to collect Lean LSP (MCP) context for prompts.

We try to use pantograph (if installed) to connect to the Lean server and
retrieve goal states at lines of interest (e.g., lines containing `sorry`).
If unavailable, we return an empty string.
"""

from __future__ import annotations

from pathlib import Path
from typing import Iterable

def collect_lsp_context_safe(file_path: str, lines: Iterable[int]) -> str:
    try:
        return collect_lsp_context(file_path, list(lines))
    except Exception:
        return ""


def collect_lsp_context(file_path: str, lines: list[int]) -> str:
    try:
        import pantograph  # type: ignore
    except Exception:
        # Pantograph not available; do nothing
        return ""

    # Normalize
    fpath = str(Path(file_path).resolve())
    ctxs: list[str] = []

    # Open a Lean server via pantograph
    with pantograph.Server() as server:  # type: ignore[attr-defined]
        doc = server.open_file(fpath)
        for ln in lines:
            try:
                # Pantograph uses 1-based lines; request goal/term-goal
                goals = doc.info(ln, 1)  # column 1
                # Assemble a compact textual summary
                if goals and hasattr(goals, "type"):
                    ctxs.append(f"[line {ln}] expected: {getattr(goals, 'type', '')}")
                # Attempt full goals
                goal_state = doc.goal(ln, 1)
                if goal_state:
                    ctxs.append(f"[line {ln}] goals: {goal_state}")
            except Exception:
                # Ignore positions that fail
                continue

    return "\n".join(ctxs)

