-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_train_souvenirs (n m : Nat) (lr_pairs : List (Nat × Nat)) : List Nat := sorry

/- For any input with n segments and m positions, the result length matches m -/
-- </vc-definitions>

-- <vc-theorems>
theorem result_length_matches_m (n m : Nat) (lr_pairs : List (Nat × Nat)) :
  List.length (solve_train_souvenirs n m lr_pairs) = m := sorry

/- All values in result are non-negative -/

theorem result_values_nonnegative (n m : Nat) (lr_pairs : List (Nat × Nat)) :
  ∀ x ∈ solve_train_souvenirs n m lr_pairs, x ≥ 0 := sorry

/- First value in result is at most n -/

theorem first_value_at_most_n (n m : Nat) (lr_pairs : List (Nat × Nat)) :
  n > 0 → m > 0 → List.head! (solve_train_souvenirs n m lr_pairs) ≤ n := sorry

/- Empty input produces list of m zeros -/

theorem empty_input_produces_zeros (m : Nat) :
  solve_train_souvenirs 0 m [] = List.replicate m 0 := sorry
-- </vc-theorems>