-- <vc-helpers>
-- </vc-helpers>

def solve (n k : Nat) (nums : List Nat) (friends : List Nat) : Nat := sorry 

theorem solve_case1 : 
  solve 4 2 [1, 13, 7, 17] [1, 3] = 48 := sorry

theorem solve_case2 :
  solve 6 2 [10, 10, 10, 10, 11, 11] [3, 3] = 42 := sorry

theorem solve_case3 : 
  solve 4 4 [1000000000, 1000000000, 1000000000, 1000000000] [1, 1, 1, 1] = 8000000000 := sorry

/-
info: 48
-/
-- #guard_msgs in
-- #eval solve 4 2 [1, 13, 7, 17] [1, 3]

/-
info: 42
-/
-- #guard_msgs in
-- #eval solve 6 2 [10, 10, 10, 10, 11, 11] [3, 3]

/-
info: 8000000000
-/
-- #guard_msgs in
-- #eval solve 4 4 [1000000000, 1000000000, 1000000000, 1000000000] [1, 1, 1, 1]

-- Apps difficulty: interview
-- Assurance level: unguarded