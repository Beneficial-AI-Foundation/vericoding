/-
Insertion sort with multiset specification using binary search.
Ported from Dafny specification at:
dafny/benchmarks/dafny-bench_specs/atomizer_supported/Dafny_tmp_tmp0wu8wmfr_Heimaverkefni 3_InsertionSortMultiset_spec.dfy

This module contains specifications for binary search and insertion sort
where correctness is specified using multisets.
-/

namespace DafnyBenchmarks

/-- Binary search in a sorted array -/
def search (s : Array Int) (x : Int) : Nat :=
  let rec searchLoop (low high : Nat) : Nat :=
    if low > high then low
    else
      let mid := (low + high) / 2
      if h : mid < s.size then
        if s[mid] ≤ x then
          searchLoop (mid + 1) high
        else
          searchLoop low (mid - 1)
      else low
  termination_by high + 1 - low
  searchLoop 0 (if s.size = 0 then 0 else s.size - 1)

/-- Insert element at position in array -/
def insertAt (arr : Array Int) (pos : Nat) (elem : Int) : Array Int :=
  if pos ≥ arr.size then arr.push elem
  else
    let before := arr.extract 0 pos
    let after := arr.extract pos arr.size
    before.push elem ++ after

/-- Insertion sort implementation -/
def insertionSort (l : List Int) : Array Int :=
  let arr := Array.mk l
  let rec insertSorted (sorted : Array Int) (elem : Int) : Array Int :=
    let pos := search sorted elem
    insertAt sorted pos elem
  arr.foldl insertSorted #[]

/-- Specification for binary search -/
theorem search_spec (s : Array Int) (x : Int)
    (h_sorted : ∀ p q, 0 ≤ p → p < q → q < s.size → s[p]! ≤ s[q]!) :
    let k := search s x
    0 ≤ k ∧ k ≤ s.size ∧
    (∀ i, 0 ≤ i → i < k → i < s.size → s[i]! ≤ x) ∧
    (∀ i, k ≤ i → i < s.size → s[i]! ≥ x) := by
  sorry

/-- Specification for insertion sort -/
theorem insertionSort_spec (l : List Int) :
    let r := insertionSort l
    r.toList.toFinset = l.toFinset ∧
    ∀ p q, 0 ≤ p → p < q → q < r.size → r[p]! ≤ r[q]! := by
  sorry

end DafnyBenchmarks