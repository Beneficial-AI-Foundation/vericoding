/-
  Port of Dafny-Exercises_tmp_tmpjm75muf__Session3Exercises_ExerciseMaximum_mmaxvalue2.dfy
  
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

def mmaxvalue2 (v : Array Int) : Int :=
  sorry  -- TODO: implement function body

theorem mmaxvalue2_spec (v : Array Int) (m : Int) :=
  (h_0 : v.size>0)
  : m in v[..] ∧ ∀ k::0≤k<v.size → m≥v[k]!
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks