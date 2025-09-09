-- <vc-helpers>
-- </vc-helpers>

def solve_coal_containers (n k : Nat) (costs : List Nat) : Nat :=
sorry

theorem solve_coal_containers_single_element
  (n : Nat) (h : n > 0) :
  solve_coal_containers 1 n [0] = 1 :=
sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval solve_coal_containers 3 2 [5, 4, 7]

/-
info: 1
-/
-- #guard_msgs in
-- #eval solve_coal_containers 5 1 [5, 3, 4, 5, 6]

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible