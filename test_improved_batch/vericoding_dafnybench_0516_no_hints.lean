/-
  Port of vericoding_dafnybench_0516_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def MinOfThree (a : Int) (b : Int) (c : Int) : Int :=
  sorry  -- TODO: implement function body

theorem MinOfThree_spec (a : Int) (b : Int) (c : Int) (min : Int) :=
  : min ≤ a ∧ min ≤ b ∧ min ≤ c ∧ (min == a) ∨ (min == b) ∨ (min == c)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks