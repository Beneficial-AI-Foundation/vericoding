-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_toy_boxes (a b c d : Nat) : Array YaNot := sorry

theorem always_contains_four_parts (a b c d : Nat) :
  (solve_toy_boxes a b c d).size = 4 ∧
  ∀ x ∈ solve_toy_boxes a b c d, x = YaNot.ya ∨ x = YaNot.tidak := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem parity_constraints (a b c d : Nat) :
  ((a + b) % 2 = 0 → (solve_toy_boxes a b c d)[0]! = YaNot.tidak ∧ (solve_toy_boxes a b c d)[1]! = YaNot.tidak) ∧
  ((a + b) % 2 ≠ 0 → (solve_toy_boxes a b c d)[2]! = YaNot.tidak ∧ (solve_toy_boxes a b c d)[3]! = YaNot.tidak) := sorry

theorem zero_small_box_constraints (b c : Nat) :
  (solve_toy_boxes 0 b c 0)[0]! = YaNot.tidak ∧ (solve_toy_boxes 0 b c 0)[3]! = YaNot.tidak := sorry

theorem zero_large_box_constraints (a d : Nat) :
  (solve_toy_boxes a 0 0 d)[1]! = YaNot.tidak ∧ (solve_toy_boxes a 0 0 d)[2]! = YaNot.tidak := sorry
-- </vc-theorems>