/-
Insertion sort on sequences.
Ported from Dafny specification at:
dafny/benchmarks/dafny-bench_specs/atomizer_supported/Dafny_tmp_tmp0wu8wmfr_tests_InsertionSortSeq_spec.dfy

This module contains specifications for checking if a sequence is sorted
and for insertion sort algorithm.
-/

import NumpySpec.DafnyBenchmarks.Multiset

namespace DafnyBenchmarks

/-- Predicate to check if an array is sorted in non-decreasing order -/
def isSorted (s : Array Int) : Prop :=
  ∀ p q, 0 ≤ p → p < q → q < s.size → s[p]! ≤ s[q]!

/-- Insertion sort implementation -/
def insertionSort (s : Array Int) : Array Int :=
  let rec insertSorted (sorted : Array Int) (elem : Int) : Array Int :=
    let rec findPos (i : Nat) : Nat :=
      if h : i < sorted.size then
        if sorted[i] > elem then i
        else findPos (i + 1)
      else i
    let pos := findPos 0
    if pos ≥ sorted.size then sorted.push elem
    else
      let before := sorted.extract 0 pos
      let after := sorted.extract pos sorted.size
      before.push elem ++ after
  s.foldl insertSorted #[]

/-- Specification for insertion sort -/
theorem insertionSort_spec (s : Array Int) :
    let r := insertionSort s
    r.toList.toMultiset = s.toList.toMultiset ∧ isSorted r := by
  sorry

end DafnyBenchmarks