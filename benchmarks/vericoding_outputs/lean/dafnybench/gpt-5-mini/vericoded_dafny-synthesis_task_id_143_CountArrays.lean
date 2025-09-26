import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
theorem Nat_cast_nonneg (n : Nat) : (n : Int) ≥ 0 := by
  induction n with
  | zero => simp
  | succ k ih =>
    -- from 0 ≤ k we get 1 ≤ k + 1, and 0 ≤ 1, so 0 ≤ k + 1
    have h := add_le_add_right ih 1
    have h0 : 0 ≤ (1 : Int) := by norm_num
    exact le_trans h0 h

-- </vc-helpers>

-- <vc-definitions>
def CountArrays (arrays : Array (Array Int)) : Int :=
(arrays.size : Int)
-- </vc-definitions>

-- <vc-theorems>
theorem CountArrays_spec (arrays : Array (Array Int)) :
let count := CountArrays arrays
count ≥ 0 ∧ count = arrays.size :=
by
  dsimp [CountArrays]
  constructor
  · -- nonneg
    exact Nat_cast_nonneg arrays.size
  · -- equality (the right-hand side is coerced to Int)
    rfl

-- </vc-theorems>
