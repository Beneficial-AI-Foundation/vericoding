def solve (points : List (Nat × Nat)) : List Nat := sorry

theorem solve_output_length {points : List (Nat × Nat)} :
  points.length = (solve points).length := sorry

-- <vc-helpers>
-- </vc-helpers>

def sqrt (n : Nat) : Nat := sorry

theorem solve_output_bound {points : List (Nat × Nat)} (i : Fin points.length) :
  let (a, b) := points.get i
  let sqrt_ab := sqrt (a * b) 
  ∃ j : Fin (solve points).length, (solve points).get j ≤ 2 * sqrt_ab := sorry

theorem solve_output_nonneg {points : List (Nat × Nat)} (i : Fin (solve points).length) :
  0 ≤ (solve points).get i := sorry

theorem solve_one_input :
  solve [(1, 1)] = [0] := sorry

/-
info: [1]
-/
-- #guard_msgs in
-- #eval solve [(1, 4)]

/-
info: [12, 4]
-/
-- #guard_msgs in
-- #eval solve [(10, 5), (3, 3)]

/-
info: [0, 0, 1, 1, 2]
-/
-- #guard_msgs in
-- #eval solve [(1, 1), (1, 2), (1, 3), (1, 4), (1, 5)]

-- Apps difficulty: competition
-- Assurance level: unguarded