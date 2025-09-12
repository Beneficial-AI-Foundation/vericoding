/-
  Port of Dafny-Exercises_tmp_tmpjm75muf__Session3Exercises_ExerciseMaximum_mlastMaximum.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def mlastMaximum (v : Array Int) : Int :=
  sorry  -- TODO: implement function body

theorem mlastMaximum_spec (v : Array Int) (i : Int) :=
  (h_0 : v.size>0)
  : 0≤i<v.size ∧ ∀ k:: 0≤k<v.size → v[i]!≥v[k]! ∧ ∀ l:: i<l<v.size → v[i]!>v[l]!
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks