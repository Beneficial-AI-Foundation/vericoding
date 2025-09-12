/-
  Port of Dafny-Exercises_tmp_tmpjm75muf__Session3Exercises_ExerciseMaximum_mmaxvalue1.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def mmaximum1 (v : Array Int) : Int :=
  sorry  -- TODO: implement function body

theorem mmaximum1_spec (v : Array Int) (i : Int) :=
  (h_0 : v.size>0)
  : 0≤i<v.size ∧ ∀ k:: 0≤k<v.size → v[i]!≥v[k]!
  := by
  sorry  -- TODO: implement proof

def mmaxvalue1 (v : Array Int) : Int :=
  sorry  -- TODO: implement function body

theorem mmaxvalue1_spec (v : Array Int) (m : Int) :=
  (h_0 : v.size>0)
  : m in v[..] ∧ ∀ k::0≤k<v.size → m≥v[k]!
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks