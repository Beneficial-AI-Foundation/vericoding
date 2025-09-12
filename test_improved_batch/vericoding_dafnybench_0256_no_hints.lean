/-
  Port of vericoding_dafnybench_0256_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def partition (a : Array T) : Int :=
  sorry  -- TODO: implement function body

theorem partition_spec (a : Array T) (pivotPos : Int) :=
  (h_0 : a.size > 0)
  : 0 ≤ pivotPos < a.size ∧ ∀ i :: 0 ≤ i < pivotPos → a[i]! < a[pivotPos]! ∧ ∀ i :: pivotPos < i < a.size → a[i]! ≥ a[pivotPos]! ∧ multiset(a[..]) == multiset(old(a[..]))
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks