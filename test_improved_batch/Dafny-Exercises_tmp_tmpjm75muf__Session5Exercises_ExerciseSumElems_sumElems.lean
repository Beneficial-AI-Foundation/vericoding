/-
  Port of Dafny-Exercises_tmp_tmpjm75muf__Session5Exercises_ExerciseSumElems_sumElems.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def SumR (s : seq<int>) : Int :=
  sorry  -- TODO: implement function body

def SumL (s : seq<int>) : Int :=
  sorry  -- TODO: implement function body

def SumV (v : Array Int) (c : Int) (f : Int) : Int :=
  SumR(v[c..f])

def sumElems (v : Array Int) : Int :=
  sorry  -- TODO: implement function body

theorem sumElems_spec (v : Array Int) (sum : Int) :=
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks