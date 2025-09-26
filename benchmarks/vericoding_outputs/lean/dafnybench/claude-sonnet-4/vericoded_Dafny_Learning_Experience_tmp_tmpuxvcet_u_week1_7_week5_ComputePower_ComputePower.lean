import Mathlib
-- <vc-preamble>
def Power (n : Nat) : Nat :=
if n = 0 then 1 else 2 * Power (n-1)
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: No additional helpers needed for this implementation
-- </vc-helpers>

-- <vc-definitions>
def CalcPower (n : Nat) : Nat :=
2 * n

def ComputePower (n : Nat) : Nat :=
if n = 0 then 1 else 2 * ComputePower (n - 1)
-- </vc-definitions>

-- <vc-theorems>
theorem CalcPower_spec (n : Nat) : CalcPower n = 2*n :=
rfl

theorem ComputePower_spec (n : Nat) : ComputePower n = Power n :=
by
  induction n with
  | zero => 
    unfold ComputePower Power
    rfl
  | succ k ih => 
    unfold ComputePower Power
    simp only [Nat.add_succ_sub_one, add_zero]
    rw [ih]
-- </vc-theorems>
