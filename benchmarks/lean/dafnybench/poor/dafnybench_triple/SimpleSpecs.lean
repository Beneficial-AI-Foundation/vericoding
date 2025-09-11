/-
Simple specifications from F1a tests.
Ported from Dafny specification at:
dafny/benchmarks/dafny-bench_specs/atomizer_supported/Dafny_tmp_tmp0wu8wmfr_tests_F1a_spec.dfy

This module contains simple specifications including a function that returns
a non-positive integer and a midpoint calculation.
-/

namespace DafnyBenchmarks

/-- Function that returns a non-positive integer -/
def f : Int :=
  -1  -- Simple implementation that satisfies the spec

/-- Compute the midpoint between two integers -/
def mid (p q : Int) : Int :=
  p + (q - p) / 2

/-- Specification for f -/
theorem f_spec :
    f ≤ 0 := by
  sorry

/-- Specification for mid -/
theorem mid_spec (p q : Int) (h : p ≤ q) :
    let m := mid p q
    p ≤ m ∧ m ≤ q ∧
    m - p ≤ q - m ∧
    0 ≤ (q - m) - (m - p) ∧ (q - m) - (m - p) ≤ 1 := by
  sorry

end DafnyBenchmarks