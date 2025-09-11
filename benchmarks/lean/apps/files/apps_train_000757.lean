-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_sequence (D: Nat) : List Nat := sorry

theorem sequence_elements_positive (D: Nat) (x: Nat) :
  x ∈ solve_sequence D → x > 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sequence_elements_bounded (D: Nat) (x: Nat) :
  x ∈ solve_sequence D → x ≤ 100000 := sorry

/-
info: [3, 3, 2]
-/
-- #guard_msgs in
-- #eval solve_sequence 2

/-
info: [2, 8, 5, 1, 10]
-/
-- #guard_msgs in
-- #eval solve_sequence 5

/-
info: [5, 4, 4, 10]
-/
-- #guard_msgs in
-- #eval solve_sequence 13

/-
info: [1]
-/
-- #guard_msgs in
-- #eval solve_sequence 0
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible