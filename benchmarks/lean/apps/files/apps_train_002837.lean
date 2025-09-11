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

/-
info: 0
-/
-- #guard_msgs in
-- #eval bouncy_count 0

/-
info: 0
-/
-- #guard_msgs in
-- #eval bouncy_count 1

/-
info: 0
-/
-- #guard_msgs in
-- #eval bouncy_count 2

/-
info: 525
-/
-- #guard_msgs in
-- #eval bouncy_count 3
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded