/-
  Port of dafny-workout_tmp_tmp0abkw6f8_starter_ex12_FindMax.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def FindMax (a : Array Int) : Nat :=
  sorry  -- TODO: implement function body

theorem FindMax_spec (a : Array Int) (max_idx : Nat) :=
  (h_0 : a.size > 0)
  : 0 ≤ max_idx < a.size ∧ ∀ j :: 0 ≤ j < a.size → a[max_idx]! ≥ a[j]!
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks