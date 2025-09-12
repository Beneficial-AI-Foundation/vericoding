/-
  Port of dafny-workout_tmp_tmp0abkw6f8_starter_ex03_Abs2.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def Abs2 (x : Float) : Float :=
  sorry  -- TODO: implement function body

theorem Abs2_spec (x : Float) (y : Float) :=
  (h_0 : x == -0.5)
  : 0.0 ≤ y ∧ 0.0 ≤ x → y == x ∧ x < 0.0 → y == -x
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks