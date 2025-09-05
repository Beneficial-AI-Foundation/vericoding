/-
Selection sort with multiset specification.
Ported from Dafny specification at:
dafny/benchmarks/dafny-bench_specs/atomizer_supported/Dafny_tmp_tmp0wu8wmfr_Heimaverkefni 3_SelectionSortMultiset_spec.dfy

This module contains specifications for finding minimum in a multiset
and selection sort where correctness is specified using multisets.
-/

import dafnybench.Multiset

namespace DafnyBenchmarks

/-- Find the minimum element in a non-empty list -/
def minOfList (lst : List Int) (h : lst ≠ []) : Int := by
  -- Implementation intentionally omitted for the benchmark; to be filled by agents.
  sorry

/-- Selection sort implementation -/
def selectionSort (l : List Int) : Array Int := by
  -- Implementation intentionally omitted for the benchmark; to be filled by agents.
  sorry

/-- Specification for minOfList -/
theorem minOfList_spec (lst : List Int) (h : lst ≠ []) :
    let min := minOfList lst h
    min ∈ lst ∧ ∀ z ∈ lst, min ≤ z := by
  sorry

/-- Specification for selection sort -/
theorem selectionSort_spec (l : List Int) :
    let s := selectionSort l
    s.toList.toMultiset = l.toMultiset ∧
    ∀ p q, 0 ≤ p → p < q → q < s.size → s[p]! ≤ s[q]! := by
  sorry

end DafnyBenchmarks
