-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_minimum_tree_height (n: Nat) (xs: List Int) : Nat := sorry

theorem singleton_list_height 
  {n: Nat} (xs: List Int) (h: xs = [1]) :
  solve_minimum_tree_height n xs = 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_bounds 
  {n: Nat} (xs: List Int) (h: xs.length > 0) :
  let result := solve_minimum_tree_height n xs
  0 ≤ result ∧ result ≤ xs.length - 1 := sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval solve_minimum_tree_height 4 [1, 4, 3, 2]

/-
info: 1
-/
-- #guard_msgs in
-- #eval solve_minimum_tree_height 2 [1, 2]

/-
info: 1
-/
-- #guard_msgs in
-- #eval solve_minimum_tree_height 3 [1, 2, 3]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible