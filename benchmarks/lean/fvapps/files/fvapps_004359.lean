-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def mormons (starting reach target : Nat) : Nat := sorry

theorem mormons_non_negative (starting reach target : Nat) :
  mormons starting reach target ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem mormons_zero_if_target_leq_starting (starting reach target : Nat) :
  target ≤ starting →
  mormons starting reach target = 0 := sorry

theorem mormons_reaches_target (starting reach target : Nat) :
  starting * ((reach + 1) ^ (mormons starting reach target)) ≥ target := sorry

theorem mormons_minimal (starting reach target : Nat) :
  mormons starting reach target > 0 →
  starting * ((reach + 1) ^ (mormons starting reach target - 1)) < target := sorry
-- </vc-theorems>