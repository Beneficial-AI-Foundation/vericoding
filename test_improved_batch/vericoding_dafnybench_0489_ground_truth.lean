/-
  Port of vericoding_dafnybench_0489_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def abs (x : Int) : Int :=
  if x < 0 then -x else x

def max (a : Int) (b : Int) : Int :=
  // Fill in an expression here. if a > b then a else b


  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof

def Abs (x : Int) : Int :=
  sorry  -- TODO: implement function body

theorem Abs_spec (x : Int) (y : Int) :=
  : abs(x) == y
  := by
  sorry  -- TODO: implement proof

def TestDouble (val : Int) : Int :=
  sorry  -- TODO: implement function body

theorem TestDouble_spec (val : Int) (val2 : Int) :=
  : val2 == Double(val)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks