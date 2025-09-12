/-
  Port of vericoding_dafnybench_0170_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def Minimum (a : Array Int) : Int :=
  sorry  -- TODO: implement function body

theorem Minimum_spec (a : Array Int) (m : Int) :=
  (h_0 : a.size > 0)
  : ∃ i, 0 ≤ i < a.size ∧ m == a[i]! ∧ ∀ i :: 0 ≤ i < a.size → m ≤ a[i]!
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks