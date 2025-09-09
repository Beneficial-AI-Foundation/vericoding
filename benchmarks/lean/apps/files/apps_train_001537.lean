-- <vc-helpers>
-- </vc-helpers>

def solve_base_plans (n : Nat) (grid : List String) : Nat :=
  sorry

theorem diagonal_case (n : Nat) :
  let diagonal := List.range n |>.map (fun i =>
    String.mk (List.range n |>.map (fun j => if i = j then '1' else '0')))
  solve_base_plans n diagonal = n * (n + 1) / 2 :=
  sorry

theorem empty_grid_one :
  solve_base_plans 1 ["1"] = 1 :=
  sorry

theorem empty_grid_zero :
  solve_base_plans 1 ["0"] = 0 :=
  sorry

theorem all_zeros (n : Nat) :
  let zeros := List.replicate n (String.mk (List.replicate n '0'))
  solve_base_plans n zeros = 0 :=
  sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval solve_base_plans 2 ["10", "01"]

/-
info: 8
-/
-- #guard_msgs in
-- #eval solve_base_plans 4 ["1000", "0010", "0100", "0001"]

/-
info: 6
-/
-- #guard_msgs in
-- #eval solve_base_plans 3 ["100", "010", "001"]

-- Apps difficulty: interview
-- Assurance level: unguarded