-- <vc-preamble>
def abs (n : Int) : Int := 
  if n ≥ 0 then n else -n
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_wabbit (x1 y1 x2 y2 : Int) : Int := sorry

theorem wabbit_nonnegative (x1 y1 x2 y2 : Int) :
  solve_wabbit x1 y1 x2 y2 ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem wabbit_same_point (x y : Int) :
  solve_wabbit x y x y = 0 := sorry

theorem wabbit_symmetry (x1 y1 x2 y2 : Int) :
  solve_wabbit x1 y1 x2 y2 = solve_wabbit x2 y2 x1 y1 := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval solve_wabbit 1 2 2 2

/-
info: 4
-/
-- #guard_msgs in
-- #eval solve_wabbit 1 1 2 2

/-
info: 0
-/
-- #guard_msgs in
-- #eval solve_wabbit 69 69 69 69

/-
info: 262146
-/
-- #guard_msgs in
-- #eval solve_wabbit 1 1 131073 131073
-- </vc-theorems>

-- Apps difficulty: competition
-- Assurance level: guarded_and_plausible