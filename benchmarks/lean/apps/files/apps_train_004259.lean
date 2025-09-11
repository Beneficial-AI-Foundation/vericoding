-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_last_digit (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem last_digit_in_range (n : Nat) :
  0 ≤ get_last_digit n ∧ get_last_digit n ≤ 9 :=
  sorry

theorem last_digit_periodic (n : Nat) :
  get_last_digit n = get_last_digit (n + 60) :=
  sorry

theorem last_digit_base_cases :
  get_last_digit 0 = 0 ∧ 
  get_last_digit 1 = 1 ∧
  get_last_digit 2 = 1 :=
  sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval get_last_digit 15

/-
info: 5
-/
-- #guard_msgs in
-- #eval get_last_digit 193150

/-
info: 0
-/
-- #guard_msgs in
-- #eval get_last_digit 300
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible