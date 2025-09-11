-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calc_max_second_screen (n b : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem calc_max_second_screen_nonnegative 
  {n b : Nat} (h : b < n) : 
  calc_max_second_screen n b ≥ 0 :=
  sorry

theorem calc_max_second_screen_energy_constraint
  {n b : Nat} (h : b < n) :
  let button_presses := n/(2*b)
  let energy_left := n - b * button_presses
  energy_left ≥ 0 :=
  sorry

/-
info: 12
-/
-- #guard_msgs in
-- #eval calc_max_second_screen 10 2

/-
info: 3
-/
-- #guard_msgs in
-- #eval calc_max_second_screen 8 5

/-
info: 9
-/
-- #guard_msgs in
-- #eval calc_max_second_screen 6 1
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible