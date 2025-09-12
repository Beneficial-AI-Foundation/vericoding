/-
  Port of Dafny-Exercises_tmp_tmpjm75muf__Session4Exercises_ExercisefirstZero_mfirstCero.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def mfirstCero (v : Array Int) : Int :=
  sorry  -- TODO: implement function body

theorem mfirstCero_spec (v : Array Int) (i : Int) :=
  : 0 ≤i≤v.size ∧ ∀ j:: 0≤j<i → v[j]!≠0 ∧ i≠v.size → v[i]≠=0
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks