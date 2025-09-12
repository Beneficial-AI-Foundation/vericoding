/-
  Port of Dafny-Exercises_tmp_tmpjm75muf__Session3Exercises_ExerciseMaximum_mfirstMaximum.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def mfirstMaximum (v : Array Int) : Int :=
  sorry  -- TODO: implement function body

theorem mfirstMaximum_spec (v : Array Int) (i : Int) :=
  (h_0 : v.size>0)
  : 0≤i<v.size ∧ ∀ k:: 0≤k<v.size → v[i]!≥v[k]! ∧ ∀ l:: 0≤l<i → v[i]!>v[l]!
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks