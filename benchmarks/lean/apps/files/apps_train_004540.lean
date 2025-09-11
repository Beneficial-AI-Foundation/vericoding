-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def hotpo (n : Nat) : Nat := sorry

theorem hotpo_terminates_at_one (n : Nat) (h : n > 0) : 
  hotpo n ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem hotpo_base_case :
  hotpo 1 = 0 := sorry

theorem hotpo_positive_for_greater_than_one (n : Nat) (h : n > 1) :
  hotpo n > 0 := sorry

theorem hotpo_even_numbers (n : Nat) (h : n > 0) (heven : n % 2 = 0) :
  hotpo n = hotpo (n / 2) + 1 := sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval hotpo 1

/-
info: 5
-/
-- #guard_msgs in
-- #eval hotpo 5

/-
info: 8
-/
-- #guard_msgs in
-- #eval hotpo 6

/-
info: 15
-/
-- #guard_msgs in
-- #eval hotpo 23
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible