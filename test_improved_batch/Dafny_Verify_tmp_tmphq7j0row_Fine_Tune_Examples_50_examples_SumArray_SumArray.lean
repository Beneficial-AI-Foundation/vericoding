/-
  Port of Dafny_Verify_tmp_tmphq7j0row_Fine_Tune_Examples_50_examples_SumArray_SumArray.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def Sum (arr : Array Int) (len : Int) : Int :=
  sorry  -- TODO: implement complex function body

def SumArray (arr : Array Int) : Int :=
  sorry  -- TODO: implement function body

theorem SumArray_spec (arr : Array Int) (sum : Int) :=
  (h_0 : arr.size > 0)
  : sum == Sum(arr, arr.size)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks