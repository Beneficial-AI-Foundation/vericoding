import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- Helper lemmas for the square root implementation
lemma sqrt_spec_helper (n : Nat) : n.sqrt * n.sqrt ≤ n ∧ n < (n.sqrt + 1) * (n.sqrt + 1) := by
  constructor
  · exact Nat.sqrt_le n
  · exact Nat.lt_succ_sqrt n
-- </vc-helpers>

-- <vc-definitions>
def SquareRoot (N : Nat) : Nat :=
Nat.sqrt N
-- </vc-definitions>

-- <vc-theorems>
theorem SquareRoot_spec (N : Nat) :
let r := SquareRoot N
r * r ≤ N ∧ N < (r + 1) * (r + 1) :=
by
  simp only [SquareRoot]
  exact sqrt_spec_helper N
-- </vc-theorems>
