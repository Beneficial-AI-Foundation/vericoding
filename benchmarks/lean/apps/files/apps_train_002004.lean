-- <vc-helpers>
-- </vc-helpers>

def solve_binary_arrangement (s : String) : List Nat :=
  sorry

theorem binary_arrangement_valid_elements {num_ones num_zeros : Nat}
  (input := String.mk (List.replicate num_ones 'n' ++ List.replicate num_zeros 'z')) :
  ∀ x ∈ solve_binary_arrangement input, x = 0 ∨ x = 1 :=
  sorry

-- Apps difficulty: competition
-- Assurance level: guarded_and_plausible