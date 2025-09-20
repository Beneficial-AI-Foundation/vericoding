-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def visit_cells (n m : Nat) : List (Nat × Nat) := sorry

def is_within_bounds (coord : Nat × Nat) (n m : Nat) : Bool :=
  let (x, y) := coord
  1 ≤ x ∧ x ≤ n ∧ 1 ≤ y ∧ y ≤ m
-- </vc-definitions>

-- <vc-theorems>
theorem visit_cells_coordinates_valid (n m : Nat) :  
  ∀ coord ∈ visit_cells n m, is_within_bounds coord n m := sorry

theorem visit_cells_unique (n m : Nat) :
  ∀ i j, i ≠ j → 
  (visit_cells n m).get! i ≠ (visit_cells n m).get! j := sorry 

theorem visit_cells_complete (n m : Nat) :
  ∀ x y, 1 ≤ x ∧ x ≤ n ∧ 1 ≤ y ∧ y ≤ m →
  (x, y) ∈ visit_cells n m := sorry

theorem visit_cells_length (n m : Nat) :
  (visit_cells n m).length = n * m := sorry

theorem visit_cells_square (n : Nat) :
  (visit_cells n n).length = n * n := sorry

theorem visit_cells_1x1 :
  visit_cells 1 1 = [(1, 1)] := sorry

theorem visit_cells_2x1 :
  visit_cells 2 1 = [(1, 1), (2, 1)] ∨ 
  visit_cells 2 1 = [(2, 1), (1, 1)] := sorry
-- </vc-theorems>