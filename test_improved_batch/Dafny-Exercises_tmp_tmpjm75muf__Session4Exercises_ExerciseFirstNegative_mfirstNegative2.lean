/-
  Port of Dafny-Exercises_tmp_tmpjm75muf__Session4Exercises_ExerciseFirstNegative_mfirstNegative2.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def mfirstNegative2 (v : Array Int) : Bool :=
  sorry  -- TODO: implement function body

theorem mfirstNegative2_spec (v : Array Int) (b : Bool) :=
  : b <→ ∃ k, 0≤k<v.size ∧ v[k]!<0 ∧ b → 0≤i<v.size ∧ v[i]!<0 ∧ positive(v[0..i])
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks