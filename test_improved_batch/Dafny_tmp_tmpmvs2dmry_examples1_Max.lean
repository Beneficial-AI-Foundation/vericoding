/-
  Port of Dafny_tmp_tmpmvs2dmry_examples1_Max.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def abs (x : Int) : Int :=
  sorry  -- TODO: implement function body

def Max (x : Int) (y : Int) : Int :=
  sorry  -- TODO: implement function body

theorem Max_spec (x : Int) (y : Int) (a : Int) :=
  : a == x ∨ a == y; ∧ x > y → a == x; ∧ x ≤ y → a == y;
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks