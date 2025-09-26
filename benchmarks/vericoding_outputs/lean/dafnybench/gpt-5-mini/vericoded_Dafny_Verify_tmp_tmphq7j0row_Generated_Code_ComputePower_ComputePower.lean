import Mathlib
-- <vc-preamble>
def Power (n : Nat) : Nat :=
if n = 0 then 1 else 2 * Power (n - 1)
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- No helper functions required for these proofs.

-- </vc-helpers>

-- <vc-definitions>
def ComputePower (n : Nat) : Nat :=
Power n
-- </vc-definitions>

-- <vc-theorems>
theorem ComputePower_spec (n : Nat) :
ComputePower n = Power n :=
by rfl
-- </vc-theorems>
