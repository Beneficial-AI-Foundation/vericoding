import Mathlib
-- <vc-preamble>
def Power (n : Nat) : Nat :=
if n = 0 then 1 else 2 * Power (n - 1)
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
lemma power_eq_pow (n : Nat) : Power n = 2^n := by
  induction n with
  | zero => 
    unfold Power
    simp [pow_zero]
  | succ n ih =>
    unfold Power
    split
    · next h => 
      -- This case is impossible: n.succ ≠ 0
      cases h
    · next h =>
      -- n + 1 - 1 = n for natural numbers when n + 1 ≠ 0
      have : n + 1 - 1 = n := Nat.add_sub_cancel n 1
      rw [this, ih, pow_succ, Nat.mul_comm]
-- </vc-helpers>

-- <vc-definitions>
def ComputePower (n : Nat) : Nat :=
2^n
-- </vc-definitions>

-- <vc-theorems>
theorem ComputePower_spec (n : Nat) :
ComputePower n = Power n :=
by
  rw [ComputePower, power_eq_pow]
-- </vc-theorems>
