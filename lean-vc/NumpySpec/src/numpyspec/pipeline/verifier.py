from __future__ import annotations

"""Lean file verifier utility.

This helper is *very* lightweight – it simply shell-outs to `lean --make` to
compile the target file and then performs a heuristic static scan to ensure
that **every** `def` / `theorem` has an accompanying documentation block that
we interpret as the *specification*.

The check is intentionally opinionated and easy to relax if your project uses a
different convention for specs (e.g. dedicated `@[spec]` attributes).  The rule
implemented here is:

    A declaration line starting with `def` or `theorem` must be preceded –
    without an intervening blank line – by either

        1. A `/-! … -/` doc-comment block, or
        2. A single-line comment beginning with `--` that contains the word
           "spec" (case-insensitive).

This keeps things simple while still catching missing specifications in most
cases.
"""

from pathlib import Path
import re
import subprocess
from typing import List

__all__ = ["verify_lean_file"]


_DECL_RE = re.compile(r"^(def|theorem)\s+([A-Za-z0-9_'.]+)")
_DOCBLOCK_START_RE = re.compile(r"/\-!")  # doc-comment block
_SPEC_LINE_RE = re.compile(r"--.*spec", re.IGNORECASE)


class VerificationError(Exception):
    """Raised when a Lean source file fails verification."""


def _run_lean_make(filepath: Path) -> None:
    """Run `lean --make <file>` and raise if compilation fails."""

    try:
        subprocess.run([
            "lean",
            "--make",
            str(filepath),
        ], check=True, capture_output=True, text=True)
    except FileNotFoundError as exc:
        raise VerificationError("`lean` executable not found in PATH.") from exc
    except subprocess.CalledProcessError as exc:
        # Bubble up lean compiler output for easier debugging.
        raise VerificationError(
            f"Lean compilation failed:\n{exc.stdout}\n{exc.stderr}"
        ) from exc


def _require_specs(filepath: Path) -> None:
    """Parse *filepath* and ensure each decl has a preceding spec comment."""

    lines: List[str] = filepath.read_text(encoding="utf8").splitlines()

    missing_specs: List[str] = []

    for idx, line in enumerate(lines):
        
        match = _DECL_RE.match(line.strip())
        if not match:
            continue

        # Walk backwards to find the closest non-empty line
        j = idx - 1
        while j >= 0 and lines[j].strip() == "":
            j -= 1

        if j < 0:
            missing_specs.append(match.group(2))
            continue

        preceding = lines[j].rstrip()
        if _DOCBLOCK_START_RE.search(preceding):
            continue  # doc-comment found
        if _SPEC_LINE_RE.search(preceding):
            continue  # inline spec comment found

        # If we reach here, spec is missing.
        missing_specs.append(match.group(2))

    if missing_specs:
        raise VerificationError(
            "Missing specification comments for declarations: "
            + ", ".join(missing_specs)
        )


def verify_lean_file(filepath: str | Path) -> None:
    """Run all verification steps on the given Lean file.

    Parameters
    ----------
    filepath : str | Path
        Path to the `.lean` source file.

    Raises
    ------
    VerificationError
        If compilation fails or a spec is missing.
    """

    path = Path(filepath).expanduser().resolve()
    if not path.is_file():
        raise FileNotFoundError(str(path))

    _run_lean_make(path)
    _require_specs(path) 