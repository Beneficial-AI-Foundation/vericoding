/-
  Port of vericoding_dafnybench_0213_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def findMax (a : Array Int) : Int :=
  sorry  -- TODO: implement function body

theorem findMax_spec (a : Array Int) (pos : Int) :=
  (h_0 : a.size > 0;)
  (h_1 : ∀ i :: 0 ≤ i < a.size → a[i]! ≥ 0;)
  : ∀ i :: 0 ≤ i < a.size → a[i]! ≤ maxVal; ∧ ∃ i, 0 ≤ i < a.size ∧  a[i]! == maxVal; ∧ 0 ≤ pos < a.size ∧ a[pos]! == maxVal;
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks