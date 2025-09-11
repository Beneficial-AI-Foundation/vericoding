-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_victory_number (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem victory_number_nonnegative (n : Nat) :
  n ≥ 1 → find_victory_number n ≥ 0 :=
  sorry

theorem victory_number_one :
  find_victory_number 1 = 0 :=
  sorry

theorem victory_number_two :
  find_victory_number 2 = 2 :=
  sorry

theorem victory_number_monotone (n : Nat) :
  n > 1 → find_victory_number n ≥ find_victory_number (n-1) :=
  sorry

theorem victory_number_contains_two (n : Nat) :
  n > 2 → find_victory_number n ≥ 2 :=
  sorry

/-
info: 77
-/
-- #guard_msgs in
-- #eval find_victory_number 22

/-
info: 41
-/
-- #guard_msgs in
-- #eval find_victory_number 13

/-
info: 17
-/
-- #guard_msgs in
-- #eval find_victory_number 10
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible