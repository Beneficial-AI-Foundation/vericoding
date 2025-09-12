/-
  Port of vericoding_dafnybench_0590_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def HasOppositeSign (a : Int) (b : Int) : Bool :=
  sorry  -- TODO: implement function body

theorem HasOppositeSign_spec (a : Int) (b : Int) (result : Bool) :=
  : result <→ (a < 0 ∧ b > 0) ∨ (a > 0 ∧ b < 0)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks