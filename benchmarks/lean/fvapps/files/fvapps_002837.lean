-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def bouncyCount (m : Nat) : Nat := sorry

theorem bouncy_count_non_negative (m : Nat) :
  bouncyCount m ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem bouncy_count_upper_bound (m : Nat) (h : m ≤ 10) :
  bouncyCount m ≤ 10^m := sorry

theorem bouncy_count_monotone (m : Nat) :
  bouncyCount m ≤ bouncyCount (m + 1) := sorry

theorem bouncy_count_zero_small_inputs :
  ∀ m : Nat, m < 3 → bouncyCount m = 0 := sorry
-- </vc-theorems>