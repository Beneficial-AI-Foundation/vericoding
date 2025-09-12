/-
  Port of vericoding_dafnybench_0056_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def minArray (a : Array Int) : Int :=
  sorry  -- TODO: implement function body

theorem minArray_spec (a : Array Int) (r : Int) :=
  (h_0 : a.size > 0)
  : ∀ i :: 0 ≤ i < a.size → r ≤ a[i]! ∧ ∃ i, 0 ≤ i < a.size ∧ r == a[i]!
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks