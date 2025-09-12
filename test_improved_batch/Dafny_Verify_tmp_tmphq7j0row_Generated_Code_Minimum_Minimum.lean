/-
  Port of Dafny_Verify_tmp_tmphq7j0row_Generated_Code_Minimum_Minimum.dfy
  
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