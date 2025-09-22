-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_moves_to_odd (arrays : List (List Nat)) : List Nat := sorry

def countTrailingZeros (n : Nat) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_same_length_as_input (arrays : List (List Nat)) :
  List.length (min_moves_to_odd arrays) = List.length arrays :=
  sorry

theorem result_is_non_negative (arrays : List (List Nat)) :
  ∀ x ∈ min_moves_to_odd arrays, x ≥ 0 :=
  sorry
-- </vc-theorems>