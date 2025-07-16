/-
Sum of integers from 0 to n.
Ported from Dafny specification at:
dafny/benchmarks/dafny-bench_specs/atomizer_supported/Dafny_tmp_tmp0wu8wmfr_tests_SumIntsLoop_spec.dfy

This module contains specifications for computing the sum of integers
from 0 to n using both recursive definition and iterative implementation.
-/

namespace DafnyBenchmarks

/-- Recursive function to compute sum of integers from 0 to n -/
def sumInts : Nat → Nat
  | 0 => 0
  | n + 1 => sumInts n + (n + 1)

/-- Iterative implementation of sum of integers -/
def sumIntsLoop (n : Nat) : Nat :=
  let rec loop (i : Nat) (acc : Nat) : Nat :=
    if i > n then acc
    else loop (i + 1) (acc + i)
  termination_by n + 1 - i
  loop 1 0

/-- Specification for sumIntsLoop -/
theorem sumIntsLoop_spec (n : Nat) :
    sumIntsLoop n = sumInts n ∧ sumIntsLoop n = n * (n + 1) / 2 := by
  sorry

end DafnyBenchmarks