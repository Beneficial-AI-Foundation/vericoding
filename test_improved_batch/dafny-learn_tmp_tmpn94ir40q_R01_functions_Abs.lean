/-
  Port of dafny-learn_tmp_tmpn94ir40q_R01_functions_Abs.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def abs (x : Int) : Int :=
  if x < 0 then -x else x

def max (a : Int) (b : Int) : Int :=
  // Fill in an expression here. if a > b then a else b

def Abs (x : Int) : Int :=
  sorry  -- TODO: implement function body

theorem Abs_spec (x : Int) (y : Int) :=
  : abs(x) == y
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks