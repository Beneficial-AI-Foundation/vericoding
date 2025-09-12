/-
  Port of Clover_abs_Abs.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def Abs (x : Int) : Int :=
  sorry  -- TODO: implement function body

theorem Abs_spec (x : Int) (y : Int) :=
  : x≥0 → x==y ∧ x<0 → x+y==0
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks