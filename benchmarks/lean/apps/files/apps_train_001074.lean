-- <vc-helpers>
-- </vc-helpers>

def count_odd_button_sums (n : Nat) (buttons : List Nat) : Nat := sorry

theorem result_non_negative (n : Nat) (buttons : List Nat) :
  count_odd_button_sums n buttons ≥ 0 := sorry

theorem single_button_gives_zero (n : Nat) :
  count_odd_button_sums 1 [n] = 0 := sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval count_odd_button_sums 4 [3, 5, 3, 4]

/-
info: 0
-/
-- #guard_msgs in
-- #eval count_odd_button_sums 2 [5, 7]

/-
info: 0
-/
-- #guard_msgs in
-- #eval count_odd_button_sums 1 [4]

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible