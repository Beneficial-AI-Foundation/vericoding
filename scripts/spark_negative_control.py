#!/usr/bin/env python3
"""Negative control for the SPARK track's harness.

A verification harness that never says "no" is worthless, so this script
mutates a known-good reference solution four ways and asserts the harness
rejects each one:

  wrong        an off-by-one implementation that violates the postcondition
  cheat        a body that assumes its way past the proof (pragma Assume)
  hollow       a body excluded from analysis (SPARK_Mode => Off), which
               GNATprove reports cleanly because it never looked at it
  broken       a body that does not compile

The "hollow" case is the one worth naming: GNATprove exits 0 with an empty
summary for code it never analysed.  A harness that only checks the exit
status and the unproved count scores that as a pass.  The driver requires a
non-zero check count for exactly this reason.

Usage:
    python scripts/spark_negative_control.py [--task FILE.ada]
"""

from __future__ import annotations

import argparse
import re
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from spark_verify import verify  # noqa: E402

DEFAULT_TASK = (
    Path(__file__).resolve().parent.parent
    / "benchmarks/spark/numpy_simple/solutions/NpAbs-spec.ada"
)

CODE_RE = re.compile(r"(--\s*<vc-code>\n)(.*?)(--\s*</vc-code>)", re.DOTALL)


def replace_code(text: str, new_body: str) -> str:
    return CODE_RE.sub(lambda m: m.group(1) + new_body + m.group(3), text)


MUTANTS: dict[str, tuple[str, set[str]]] = {
    "wrong": (
        """   procedure Abs_Vec (A : Int_Array; Result : out Int_Array) is
   begin
      Result := (others => 0);
      for I in A'Range loop
         Result (I) := A (I);
         pragma Loop_Invariant
           (for all J in A'First .. I => Result (J) = A (J));
      end loop;
   end Abs_Vec;
""",
        {"unproved"},
    ),
    "cheat": (
        """   procedure Abs_Vec (A : Int_Array; Result : out Int_Array) is
   begin
      Result := (others => 0);
      pragma Assume (for all I in A'Range => Result (I) = Abs_Int (A (I)));
   end Abs_Vec;
""",
        {"cheat"},
    ),
    "hollow": (
        """   procedure Abs_Vec (A : Int_Array; Result : out Int_Array)
     with SPARK_Mode => Off
   is
   begin
      Result := (others => 0);
   end Abs_Vec;
""",
        {"cheat", "no_checks"},
    ),
    "broken": (
        """   procedure Abs_Vec (A : Int_Array; Result : out Int_Array) is
   begin
      Result := (others => 0)
      for I in A'Range loop
   end Abs_Vec;
""",
        {"compile_error"},
    ),
}


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--task", type=Path, default=DEFAULT_TASK)
    args = parser.parse_args(argv)

    reference = args.task.read_text(encoding="utf-8")

    baseline = verify(args.task)
    print(f"baseline (unmutated reference): {baseline.status} "
          f"({baseline.total_checks} checks)")
    failures = 0
    if not baseline.ok:
        print("  !! the reference solution itself does not pass; "
              "the control proves nothing")
        failures += 1

    workdir = Path(tempfile.mkdtemp(prefix="spark_negctl_"))
    for label, (body, expected) in MUTANTS.items():
        path = workdir / f"{args.task.stem}-{label}.ada"
        path.write_text(replace_code(reference, body), encoding="utf-8")
        verdict = verify(path)
        rejected = not verdict.ok and verdict.status in expected
        mark = "OK  " if rejected else "MISS"
        print(f"{mark} mutant '{label}': harness said '{verdict.status}' "
              f"(expected one of {sorted(expected)})")
        if verdict.detail:
            print(f"       {verdict.detail.splitlines()[0][:140]}")
        if not rejected:
            failures += 1

    print()
    if failures:
        print(f"NEGATIVE CONTROL FAILED: {failures} case(s) not handled")
        return 1
    print("NEGATIVE CONTROL PASSED: reference accepted, all four mutants rejected")
    return 0


if __name__ == "__main__":
    sys.exit(main())
