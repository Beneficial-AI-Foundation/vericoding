import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
lemma nat_sqrt_mul_self_le (n : Nat) : Nat.sqrt n * Nat.sqrt n ≤ n := by
  simpa using (Nat.le_sqrt.1 (le_rfl : Nat.sqrt n ≤ Nat.sqrt n))

-- LLM HELPER
lemma nat_lt_succ_sqrt_mul (n : Nat) : n < (Nat.sqrt n + 1) * (Nat.sqrt n + 1) := by
  simpa [pow_two] using Nat.lt_succ_sqrt n
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
  simpa [SquareRoot] using
    And.intro
      (nat_sqrt_mul_self_le N)
      (nat_lt_succ_sqrt_mul N)
-- </vc-theorems>
