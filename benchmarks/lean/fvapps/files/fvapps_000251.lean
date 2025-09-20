-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def jump (v : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem jump_single_element (n : Nat) :
  jump [n] = 0 :=
  sorry

theorem jump_two_elements :
  jump [2, 1] = 1 :=
  sorry

theorem jump_three_ones :
  jump [1, 1, 1] = 2 :=
  sorry

theorem jump_complex_case1 :
  jump [2, 3, 1, 1, 4] = 2 :=
  sorry

theorem jump_complex_case2 :
  jump [2, 1, 1, 1] = 2 :=
  sorry

theorem jump_ascending :
  jump [1, 2, 3] = 2 :=
  sorry

theorem jump_long_sequence :
  jump [5, 9, 3, 2, 1, 0, 2, 3, 3, 1, 0, 0] = 3 :=
  sorry

theorem jump_descending :
  jump [3, 2, 1] = 1 :=
  sorry

theorem jump_mixed_sequence :
  jump [4, 1, 1, 3, 1, 1, 1] = 2 :=
  sorry
-- </vc-theorems>