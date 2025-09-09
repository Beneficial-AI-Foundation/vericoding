-- <vc-helpers>
-- </vc-helpers>

def solve_scarf_xor (n : Nat) (a : List Nat) : List Nat := sorry

theorem result_length_matches_input (n : Nat) (a : List Nat) 
  (h : n ≥ 2) :
  let result := solve_scarf_xor n a
  List.length result = n := sorry

theorem result_elements_nonnegative (n : Nat) (a : List Nat) 
  (h : n ≥ 2) :
  let result := solve_scarf_xor n a
  ∀ x ∈ result, x ≥ 0 := sorry

theorem zero_array_maps_to_zeros (n : Nat)
  (h : n ≥ 2) :
  let zeros := List.replicate n 0
  let result := solve_scarf_xor n zeros
  ∀ x ∈ result, x = 0 := sorry

-- Apps difficulty: interview
-- Assurance level: guarded