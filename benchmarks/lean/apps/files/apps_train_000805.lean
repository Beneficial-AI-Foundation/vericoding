-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_barbecue_sticks (n: Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem bbq_sticks_positive (n: Nat) (h: n ≥ 3): 
  solve_barbecue_sticks n > 0 :=
  sorry

theorem bbq_sticks_odd (n: Nat) (h: n ≥ 3):
  solve_barbecue_sticks n % 2 = 1 :=
  sorry 

theorem bbq_sticks_exponential_growth (n: Nat) (h: n ≥ 3):
  solve_barbecue_sticks n ≥ 2^(n-2) :=
  sorry

theorem bbq_sticks_strictly_increasing {n: Nat} (h: n > 3):
  solve_barbecue_sticks n > solve_barbecue_sticks (n-1) :=
  sorry

/-
info: 5
-/
-- #guard_msgs in
-- #eval solve_barbecue_sticks 4

/-
info: 9
-/
-- #guard_msgs in
-- #eval solve_barbecue_sticks 5

/-
info: 17
-/
-- #guard_msgs in
-- #eval solve_barbecue_sticks 6
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible