/-
  Port of Dafny_tmp_tmpmvs2dmry_examples1_Abs.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def abs (x : Int) : Int :=
  sorry  -- TODO: implement function body

def Abs (x : Int) : Int :=
  sorry  -- TODO: implement function body

theorem Abs_spec (x : Int) (y : Int) :=
  : y≥0; ∧ x≥0 → x == y; ∧ x<0 → -x == y; ∧ y == abs(x); // use this instead of line 3,4
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks