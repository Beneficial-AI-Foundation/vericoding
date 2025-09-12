/-
  Port of formal_verication_dafny_tmp_tmpwgl2qz28_Challenges_ex2_Allow42.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def Allow42 (x : Int) (y : Int) : Int :=
  sorry  -- TODO: implement function body

theorem Allow42_spec (x : Int) (y : Int) (z : Int) :=
  : y ≠ 42 → z == x/(42-y) ∧ err == false; ∧ y == 42 → z == 0 ∧ err == true;
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks