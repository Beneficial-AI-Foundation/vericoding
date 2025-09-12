/-
  Port of Dafny-Exercises_tmp_tmpjm75muf__Session6Exercises_ExercisePeekSum_mPeekSum.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def peekSum (v : Array Int) (i : Int) : Int :=
  sorry  -- TODO: implement function body

def mPeekSum (v : Array Int) : Int :=
  sorry  -- TODO: implement function body

theorem mPeekSum_spec (v : Array Int) (sum : Int) :=
  (h_0 :  v.size>0)
  : sum==peekSum(v,v.size)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks