#!/usr/bin/env python3
"""Verification driver for the SPARK/Ada track.

A SPARK task file is a single GNAT multi-unit source (``.ada``) holding a
package spec followed by its body, with the usual vericoding section markers
written as Ada comments::

    --  <vc-preamble> ... --  </vc-preamble>
    --  <vc-spec>     ... --  </vc-spec>
    --  <vc-helpers>  ... --  </vc-helpers>
    --  <vc-code>     ... --  </vc-code>
    --  <vc-postamble> ... --  </vc-postamble>

The driver chops the file into the ``.ads``/``.adb`` pair GNAT expects,
writes a throwaway project file, and runs ``gnatprove``.  A task passes iff
GNATprove analysed it, emitted at least one check, and left nothing unproved
or justified.

Usage:
    python scripts/spark_verify.py FILE.ada [--level N] [--timeout S] [--json]

Exit status is 0 for a pass and 1 for a failure, so the script can be used
directly as a gate in a shell pipeline.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from dataclasses import dataclass, asdict
from pathlib import Path

# --------------------------------------------------------------------------
# Cheat patterns
#
# The SPARK analogues of Dafny's ``assume {:axiom} false`` and Lean's
# ``sorry``.  Each of these lets a body "verify" without a proof, so a
# submission containing one is rejected before GNATprove is even consulted.
# --------------------------------------------------------------------------
CHEAT_PATTERNS: list[tuple[str, str]] = [
    (r"pragma\s+Assume\b", "uses 'pragma Assume' to bypass verification"),
    (
        r"pragma\s+Annotate\s*\(\s*GNATprove\s*,\s*(?:False_Positive|Intentional)",
        "justifies a check away with pragma Annotate (GNATprove, False_Positive|Intentional)",
    ),
    (
        r"SPARK_Mode\s*(?:=>|\()\s*Off",
        "switches SPARK_Mode off, removing the code from analysis",
    ),
    (
        r"pragma\s+Warnings\s*\(\s*Off",
        "suppresses warnings, which can hide analysis messages",
    ),
    (
        r"pragma\s+Suppress\b",
        "suppresses run-time checks instead of proving them",
    ),
    (
        r"\bUnchecked_Conversion\b",
        "uses Unchecked_Conversion to escape the type system",
    ),
    (
        r"pragma\s+Import\b",
        "imports an external body that GNATprove cannot analyse",
    ),
]

SECTION_RE = re.compile(
    r"--\s*<(?P<name>vc-[a-z]+)>\s*\n(?P<body>.*?)\n?[ \t]*--\s*</(?P=name)>",
    re.DOTALL,
)

EDITABLE_SECTIONS = ("vc-helpers", "vc-code")

GPR_TEMPLATE = """project Verify is
   for Source_Dirs use (".");
   for Object_Dir use "obj";
   package Compiler is
      for Default_Switches ("Ada") use ("-gnat2022", "-gnatwa");
   end Compiler;
end Verify;
"""


@dataclass
class Verdict:
    """Outcome of verifying one SPARK task file."""

    file: str
    status: str  # "pass" | "cheat" | "compile_error" | "no_checks" | "unproved" | "tool_error"
    total_checks: int = 0
    flow_checks: int = 0
    prover_checks: int = 0
    justified: int = 0
    unproved: int = 0
    detail: str = ""

    @property
    def ok(self) -> bool:
        return self.status == "pass"


def parse_sections(text: str) -> dict[str, str]:
    """Return the vc-* sections found in a task file, keyed by tag name."""
    return {m.group("name"): m.group("body") for m in SECTION_RE.finditer(text)}


def check_for_cheats(text: str) -> list[tuple[str, str]]:
    """Detect verification bypasses in the editable sections of a task file.

    Bypasses are tolerated outside the editable sections because the
    unfilled template itself carries a ``pragma Assume (False)`` placeholder,
    exactly as the Dafny templates carry ``assume {:axiom} false``.
    """
    sections = parse_sections(text)
    editable = "\n".join(sections.get(name, "") for name in EDITABLE_SECTIONS)
    # If the file carries no markers at all, scrutinise the whole thing.
    haystack = editable if sections else text
    found = []
    for pattern, description in CHEAT_PATTERNS:
        if re.search(pattern, haystack, re.IGNORECASE):
            found.append((pattern, description))
    return found


SUMMARY_TOTAL_RE = re.compile(r"^Total\s+(\d+)(.*)$", re.MULTILINE)


def parse_summary(summary_text: str) -> tuple[int, int, int, int]:
    """Parse GNATprove's summary table.

    Returns ``(total, flow, justified, unproved)``.  Empty columns are
    printed as ``.`` by GNATprove and read back as zero.
    """
    match = SUMMARY_TOTAL_RE.search(summary_text)
    if not match:
        return (0, 0, 0, 0)
    total = int(match.group(1))
    columns = [c.strip() for c in re.split(r"\s{2,}", match.group(2).strip()) if c.strip()]

    def leading_int(cell: str) -> int:
        m = re.match(r"(\d+)", cell)
        return int(m.group(1)) if m else 0

    # Columns after Total are: Flow, Provers, Justified, Unproved.  Trailing
    # empty columns are dropped by the splitter, so index from the front and
    # tolerate a short row.
    flow = leading_int(columns[0]) if len(columns) > 0 else 0
    justified = leading_int(columns[2]) if len(columns) > 2 else 0
    unproved = leading_int(columns[3]) if len(columns) > 3 else 0
    return (total, flow, justified, unproved)


def verify(path: Path, level: int = 2, timeout: int = 900, keep: bool = False) -> Verdict:
    """Chop, prove and judge a single SPARK task file."""
    text = path.read_text(encoding="utf-8")

    cheats = check_for_cheats(text)
    if cheats:
        return Verdict(
            file=str(path),
            status="cheat",
            detail="; ".join(description for _, description in cheats),
        )

    workdir = Path(tempfile.mkdtemp(prefix="spark_verify_"))
    try:
        source = workdir / path.name
        shutil.copy(path, source)
        obj = workdir / "obj"
        obj.mkdir()
        (workdir / "verify.gpr").write_text(GPR_TEMPLATE, encoding="utf-8")

        chop = subprocess.run(
            ["gnatchop", "-q", "-w", source.name],
            cwd=workdir,
            capture_output=True,
            text=True,
            timeout=timeout,
        )
        if chop.returncode != 0:
            return Verdict(
                file=str(path),
                status="compile_error",
                detail=f"gnatchop failed: {(chop.stderr or chop.stdout).strip()[:2000]}",
            )
        source.unlink()  # the chopped units replace the multi-unit source

        proof = subprocess.run(
            [
                "gnatprove",
                "-P",
                "verify.gpr",
                f"--level={level}",
                "--report=all",
                "--checks-as-errors=on",
                "-q",
            ],
            cwd=workdir,
            capture_output=True,
            text=True,
            timeout=timeout,
        )
        output = (proof.stdout or "") + (proof.stderr or "")

        if re.search(r"^\S+:\d+:\d+: error:", output, re.MULTILINE) or "cannot be parsed" in output:
            return Verdict(
                file=str(path),
                status="compile_error",
                detail=output.strip()[:2000],
            )

        summary_path = obj / "gnatprove" / "gnatprove.out"
        if not summary_path.is_file():
            return Verdict(
                file=str(path),
                status="tool_error",
                detail=f"no gnatprove summary produced; output: {output.strip()[:2000]}",
            )

        total, flow, justified, unproved = parse_summary(
            summary_path.read_text(encoding="utf-8", errors="replace")
        )

        # A body that generates no checks at all is not a proof.  GNATprove
        # reports a clean run for code it never actually analysed (an empty
        # SPARK_Mode region, say), so an empty check count is treated as a
        # failure rather than a pass.
        if total == 0:
            return Verdict(
                file=str(path),
                status="no_checks",
                total_checks=0,
                detail="GNATprove generated no checks; nothing was actually verified",
            )

        if unproved or justified:
            return Verdict(
                file=str(path),
                status="unproved",
                total_checks=total,
                flow_checks=flow,
                prover_checks=total - flow,
                justified=justified,
                unproved=unproved,
                detail=_collect_messages(output)[:2000],
            )

        return Verdict(
            file=str(path),
            status="pass",
            total_checks=total,
            flow_checks=flow,
            prover_checks=total - flow,
            justified=justified,
            unproved=unproved,
        )
    except subprocess.TimeoutExpired:
        return Verdict(file=str(path), status="tool_error", detail=f"timed out after {timeout}s")
    finally:
        if keep:
            print(f"[kept workdir] {workdir}", file=sys.stderr)
        else:
            shutil.rmtree(workdir, ignore_errors=True)


def _collect_messages(output: str) -> str:
    """Pull the medium/high diagnostic lines out of a GNATprove run."""
    lines = [
        line
        for line in output.splitlines()
        if re.search(r":\s*(medium|high|error|warning):", line)
    ]
    return "\n".join(lines) if lines else output.strip()


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Verify a SPARK vericoding task file.")
    parser.add_argument("files", nargs="+", type=Path, help="task .ada file(s)")
    parser.add_argument("--level", type=int, default=2, help="gnatprove --level (default 2)")
    parser.add_argument("--timeout", type=int, default=900, help="per-file timeout in seconds")
    parser.add_argument("--json", action="store_true", help="emit JSON lines")
    parser.add_argument("--keep", action="store_true", help="keep the temporary work directory")
    args = parser.parse_args(argv)

    if shutil.which("gnatprove") is None or shutil.which("gnatchop") is None:
        print("gnatprove and gnatchop must be on PATH (install SPARK, e.g. via Alire)", file=sys.stderr)
        return 2

    failures = 0
    for path in args.files:
        verdict = verify(path, level=args.level, timeout=args.timeout, keep=args.keep)
        if args.json:
            print(json.dumps(asdict(verdict)))
        else:
            mark = "PASS" if verdict.ok else "FAIL"
            extra = f"{verdict.total_checks} checks, {verdict.unproved} unproved"
            print(f"{mark}  {path.name}  [{verdict.status}]  {extra}")
            if verdict.detail:
                for line in verdict.detail.splitlines()[:12]:
                    print(f"        {line}")
        if not verdict.ok:
            failures += 1

    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
