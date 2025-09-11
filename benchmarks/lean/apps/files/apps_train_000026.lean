-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_jigsaw (n m : Nat) : Bool := sorry

theorem solve_jigsaw_symmetry (n m : Nat) :
  solve_jigsaw n m = solve_jigsaw m n := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_jigsaw_one_row (n : Nat) : 
  solve_jigsaw 1 n = true := sorry

theorem solve_jigsaw_2x2 :
  solve_jigsaw 2 2 = true := sorry

theorem solve_jigsaw_large_grids (n m : Nat) :
  n ≥ 3 → m ≥ 3 → solve_jigsaw n m = false := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval solve_jigsaw 1 3

/-
info: False
-/
-- #guard_msgs in
-- #eval solve_jigsaw 100000 100000

/-
info: True
-/
-- #guard_msgs in
-- #eval solve_jigsaw 2 2
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded