/-
  Port of dafny-workout_tmp_tmp0abkw6f8_starter_ex03_Abs.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def Abs (x : Int) : Int :=
  sorry  -- TODO: implement function body

theorem Abs_spec (x : Int) (y : Int) :=
  (h_0 : x == -1)
  : 0 ≤ y ∧ 0 ≤ x → y == x ∧ x < 0 → y == -x
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks