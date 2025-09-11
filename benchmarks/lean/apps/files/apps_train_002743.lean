-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def cumulative_triangle (n : Nat) : Nat := sorry

theorem cumulative_triangle_positive (n : Nat) (h : n > 0) :
  cumulative_triangle n > 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem cumulative_triangle_strictly_increasing (n : Nat) (h : n > 1) :
  cumulative_triangle n > cumulative_triangle (n - 1) := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval cumulative_triangle 1

/-
info: 5
-/
-- #guard_msgs in
-- #eval cumulative_triangle 2

/-
info: 15
-/
-- #guard_msgs in
-- #eval cumulative_triangle 3

/-
info: 34
-/
-- #guard_msgs in
-- #eval cumulative_triangle 4
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible