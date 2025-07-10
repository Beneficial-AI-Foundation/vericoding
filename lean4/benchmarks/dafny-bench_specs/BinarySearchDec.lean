/-
Binary search on a decreasing sequence.
Ported from Dafny specification at:
dafny/benchmarks/dafny-bench_specs/atomizer_supported/Dafny_tmp_tmp0wu8wmfr_Heimaverkefni 2_BinarySearchDec_spec.dfy

This module contains specifications for searching in a decreasing sequence.
The sequence is sorted in descending order (larger values come first).
-/

namespace DafnyBenchmarks

/-- Recursive binary search on a decreasing sequence -/
def searchRecursive (a : Array Float) (i j : Nat) (x : Float) : Nat :=
  if h : i ≥ j then i
  else
    let mid := (i + j) / 2
    if hm : mid < a.size then
      if a[mid] ≥ x then
        if mid < j then
          searchRecursive a mid j x
        else i
      else
        if i < mid then
          searchRecursive a i mid x
        else i
    else i
termination_by j - i

/-- Iterative binary search on a decreasing sequence -/
def searchLoop (a : Array Float) (i j : Nat) (x : Float) : Nat :=
  let rec loop (low high : Nat) : Nat :=
    if low ≥ high then low
    else
      let mid := (low + high) / 2
      if hm : mid < a.size then
        if a[mid] ≥ x then
          if mid < high then
            loop mid high
          else low
        else
          if low < mid then
            loop low mid
          else low
      else low
  termination_by high - low
  loop i j

/-- Specification for recursive binary search -/
theorem searchRecursive_spec (a : Array Float) (i j : Nat) (x : Float) 
    (h_bounds : 0 ≤ i ∧ i ≤ j ∧ j ≤ a.size)
    (h_sorted : ∀ p q, i ≤ p → p < q → q < j → p < a.size → q < a.size → a[p]! ≥ a[q]!) :
    let k := searchRecursive a i j x
    i ≤ k ∧ k ≤ j ∧
    (∀ r, i ≤ r → r < k → r < a.size → a[r]! ≥ x) ∧
    (∀ r, k ≤ r → r < j → r < a.size → a[r]! < x) := by
  sorry

/-- Specification for iterative binary search -/
theorem searchLoop_spec (a : Array Float) (i j : Nat) (x : Float)
    (h_bounds : 0 ≤ i ∧ i ≤ j ∧ j ≤ a.size)
    (h_sorted : ∀ p q, i ≤ p → p < q → q < j → p < a.size → q < a.size → a[p]! ≥ a[q]!) :
    let k := searchLoop a i j x
    i ≤ k ∧ k ≤ j ∧
    (∀ r, i ≤ r → r < k → r < a.size → a[r]! ≥ x) ∧
    (∀ r, k ≤ r → r < j → r < a.size → a[r]! < x) := by
  sorry

end DafnyBenchmarks