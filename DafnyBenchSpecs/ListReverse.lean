/-
List reversal with proofs.
Ported from Dafny specification at:
dafny/benchmarks/dafny-bench_specs/atomizer_supported/dafny_tmp_tmp2ewu6s7x_ListReverse_spec.dfy

This module contains the reverse function for sequences and lemmas about its properties,
including that reverse distributes over append and that reverse is an involution.
-/

namespace DafnyBenchmarks

/-- Recursive definition of list reversal -/
def reverse : List Nat → List Nat
  | [] => []
  | x :: xs => reverse xs ++ [x]

/-- Lemma: reverse distributes over append -/
theorem reverseAppendDistr (xs ys : List Nat) :
  reverse (xs ++ ys) = reverse ys ++ reverse xs := by
  sorry

/-- Lemma: reverse is an involution (applying it twice gives the original) -/
theorem reverseInvolution (xxs : List Nat) :
  reverse (reverse xxs) = xxs := by
  sorry

end DafnyBenchmarks