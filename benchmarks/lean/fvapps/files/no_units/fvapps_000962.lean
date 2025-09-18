-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_dishes (n k q : Nat) (array_params : Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat)
  (range_params : Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat) : Nat × Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_dishes_output_is_pair (n k q : Nat) 
  (array_params : Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat)
  (range_params : Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat) :
  ∃ (x y : Nat), solve_dishes n k q array_params range_params = (x, y) := sorry

theorem solve_dishes_first_nonneg (n k q : Nat)
  (array_params : Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat) 
  (range_params : Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat) :
  (solve_dishes n k q array_params range_params).1 ≥ 0 := sorry

theorem solve_dishes_second_bounded (n k q : Nat)
  (array_params : Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat)
  (range_params : Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat) :
  (solve_dishes n k q array_params range_params).2 < 10^9 + 7 := sorry

theorem solve_dishes_second_nonneg (n k q : Nat)
  (array_params : Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat)
  (range_params : Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat) :
  (solve_dishes n k q array_params range_params).2 ≥ 0 := sorry
-- </vc-theorems>