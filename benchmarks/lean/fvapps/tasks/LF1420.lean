-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_special_numbers (n: Nat) : Nat × Nat := sorry

theorem edge_case_one :
  count_special_numbers 1 = (0, 1) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem small_case_three :
  count_special_numbers 3 = (1, 20) := sorry

theorem small_case_five :
  count_special_numbers 5 = (1, 20) := sorry
-- </vc-theorems>