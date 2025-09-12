/-
  Port of Clover_max_array_maxArray.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def maxArray (a : Array Int) : Int :=
  sorry  -- TODO: implement function body

theorem maxArray_spec (a : Array Int) (m : Int) :=
  (h_0 : a.size ≥ 1)
  : ∀ k :: 0 ≤ k < a.size → m ≥ a[k]! ∧ ∃ k, 0 ≤ k < a.size ∧ m == a[k]!
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks