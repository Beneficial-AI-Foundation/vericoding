/-
  Port of dafny-synthesis_task_id_801_CountEqualNumbers.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def CountEqualNumbers (a : Int) (b : Int) (c : Int) : Int :=
  sorry  -- TODO: implement function body

theorem CountEqualNumbers_spec (a : Int) (b : Int) (c : Int) (count : Int) :=
  : count ≥ 0 ∧ count ≤ 3 ∧ (count == 3) <→ (a == b ∧ b == c) ∧ (count == 2) <→ ((a == b ∧ b ≠ c) ∨ (a ≠ b ∧ b == c) ∨ (a == c ∧ b ≠ c)) ∧ (count == 1) <→ (a ≠ b ∧ b ≠ c ∧ a ≠ c)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks