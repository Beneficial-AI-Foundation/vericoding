-- <vc-helpers>
-- </vc-helpers>

def calc_min_cleaning_rounds (x y : Int) : Nat :=
  sorry

theorem min_cleaning_rounds_bounds (x y : Int) : 
  let result := calc_min_cleaning_rounds x y
  0 ≤ result ∧ result ≤ 3 :=
  sorry

theorem same_input_zero (x : Int) :
  calc_min_cleaning_rounds x x = 0 :=
  sorry

theorem multiple_four_diff_equals_three (x : Int) :
  calc_min_cleaning_rounds x (x + 4) = 3 :=
  sorry

theorem parity_cleaning_rounds (x y : Int) :
  let result := calc_min_cleaning_rounds x y
  let diff := y - x
  (y > x → (diff % 2 = 0 → result = 2 ∨ result = 3) ∧ 
           (diff % 2 ≠ 0 → result = 1)) ∧
  (y < x → (diff % 2 = 0 → result = 1) ∧
           (diff % 2 ≠ 0 → result = 2)) :=
  sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval calc_min_cleaning_rounds 0 5

/-
info: 2
-/
-- #guard_msgs in
-- #eval calc_min_cleaning_rounds 4 -5

/-
info: 1
-/
-- #guard_msgs in
-- #eval calc_min_cleaning_rounds 0 10000001

-- Apps difficulty: interview
-- Assurance level: unguarded