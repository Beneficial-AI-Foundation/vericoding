/-
Dutch National Flag problem.
Ported from Dafny specification at:
dafny/benchmarks/dafny-bench_specs/atomizer_supported/dafny_tmp_tmp49a6ihvk_m4_spec.dfy

This module contains the specification for the Dutch Flag problem,
which partitions an array of colors (Red, White, Blue) such that
all reds come before whites, and all whites come before blues.
-/

import dafnybench.Multiset

namespace DafnyBenchmarks

/-- The three colors of the Dutch flag -/
inductive Color
  | Red
  | White
  | Blue
deriving DecidableEq, Inhabited

/-- Predicate defining the ordering relation between colors -/
def below (c d : Color) : Bool :=
  c == Color.Red || c == d || d == Color.Blue

/-- Dutch Flag algorithm implementation -/
def dutchFlag (a : Array Color) : Array Color := by
  -- Implementation intentionally omitted for the benchmark; to be filled by agents.
  sorry

/-- Specification for the Dutch Flag algorithm -/
theorem dutchFlag_spec (a : Array Color) :
    let a' := dutchFlag a
    (∀ i j, 0 ≤ i → i < j → j < a'.size → below a'[i]! a'[j]!) ∧
    a'.toList.toMultiset = a.toList.toMultiset := by
  sorry

end DafnyBenchmarks
