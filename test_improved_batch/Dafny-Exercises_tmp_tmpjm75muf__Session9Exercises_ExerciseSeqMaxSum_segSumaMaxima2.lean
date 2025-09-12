/-
  Port of Dafny-Exercises_tmp_tmpjm75muf__Session9Exercises_ExerciseSeqMaxSum_segSumaMaxima2.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def Sum (v : Array Int) (i : Int) (j : Int) : Int :=
  sorry  -- TODO: implement function body

def Sum2 (v : Array Int) (i : Int) (j : Int) : Int :=
  sorry  -- TODO: implement function body

def segSumaMaxima2 (v : Array Int) (i : Int) : Int :=
  sorry  -- TODO: implement function body

theorem segSumaMaxima2_spec (v : Array Int) (i : Int) (s : Int) :=
  (h_0 : v.size>0 ∧ 0≤i<v.size)
  : 0≤k≤i ∧ s==Sum2(v,k,i+1) ∧  SumMaxToRight2(v,0,i,s)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks