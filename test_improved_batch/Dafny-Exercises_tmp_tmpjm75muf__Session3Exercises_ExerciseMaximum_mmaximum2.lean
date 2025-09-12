/-
  Port of Dafny-Exercises_tmp_tmpjm75muf__Session3Exercises_ExerciseMaximum_mmaximum2.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def mmaximum2 (v : Array Int) : Int :=
  sorry  -- TODO: implement function body

theorem mmaximum2_spec (v : Array Int) (i : Int) :=
  (h_0 : v.size>0)
  : 0≤i<v.size ∧ ∀ k:: 0≤k<v.size → v[i]!≥v[k]!
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks