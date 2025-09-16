-- <vc-preamble>
def sum_list : List Nat → Nat 
  | [] => 0
  | x :: xs => x + sum_list xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calculate_chef_money (rows: List (List Nat)) : Nat := sorry

theorem chef_money_nonnegative (rows: List (List Nat)) :
  calculate_chef_money rows ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
/-
info: 8
-/
-- #guard_msgs in
-- #eval calculate_chef_money [[4, 5, 2, 3, 4], [2, 1, 6]]

/-
info: 1
-/
-- #guard_msgs in
-- #eval calculate_chef_money [[2, 1, 2]]

/-
info: 12
-/
-- #guard_msgs in
-- #eval calculate_chef_money [[3, 5, 2, 3], [4, 1, 6, 4, 2]]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible