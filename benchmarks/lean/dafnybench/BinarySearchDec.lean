/-
Binary search on a decreasing sequence.
Ported from Dafny specification at:
dafny/benchmarks/dafny-bench_specs/atomizer_supported/Dafny_tmp_tmp0wu8wmfr_Heimaverkefni 2_BinarySearchDec_spec.dfy

This module contains specifications for searching in a decreasing sequence.-
The sequence is sorted in descending order (larger values come first).
-/

namespace DafnyBenchmarks

/-- Recursive binary search on a decreasing sequence -/
def searchRecursive (a : Array Int) (i j : Nat) (x : Int) : Nat := sorry

/-- Iterative binary search on a decreasing sequence -/
def searchLoop (a : Array Int) (i j : Nat) (x : Int) : Nat := sorry

/-- Specification for recursive binary search -/
theorem searchRecursive_spec (a : Array Int) (i j : Nat) (x : Int)
    (h_bounds : 0 ≤ i ∧ i ≤ j ∧ j ≤ a.size)
    (h_sorted : ∀ p q, i ≤ p → p < q → q < j → p < a.size → q < a.size → a[p]! ≥ a[q]!) :
    let k := searchRecursive a i j x
    i ≤ k ∧ k ≤ j ∧
    (∀ r, i ≤ r → r < k → r < a.size → a[r]! ≥ x) ∧
    (∀ r, k ≤ r → r < j → r < a.size → a[r]! < x) := by
  sorry

/-- Specification for iterative binary search -/
theorem searchLoop_spec (a : Array Int) (i j : Nat) (x : Int)
    (h_bounds : 0 ≤ i ∧ i ≤ j ∧ j ≤ a.size)
    (h_sorted : ∀ p q, i ≤ p → p < q → q < j → p < a.size → q < a.size → a[p]! ≥ a[q]!) :
    let k := searchLoop a i j x
    i ≤ k ∧ k ≤ j ∧
    (∀ r, i ≤ r → r < k → r < a.size → a[r]! ≥ x) ∧
    (∀ r, k ≤ r → r < j → r < a.size → a[r]! < x) := by
  sorry

end DafnyBenchmarks
