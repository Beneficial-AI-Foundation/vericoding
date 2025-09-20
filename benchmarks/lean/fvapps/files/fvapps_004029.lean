-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def difference_of_squares (n : Nat) : Nat :=
  sorry

def sum_up_to (n : Nat) : Nat :=
  sorry

def sum_squares_up_to (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem difference_non_negative {n : Nat} :
  difference_of_squares n ≥ 0 :=
sorry

theorem zero_and_one_cases :
  difference_of_squares 0 = 0 ∧ difference_of_squares 1 = 0 :=
sorry

theorem strictly_increasing {n : Nat} (h : n ≥ 2) :
  difference_of_squares n > difference_of_squares (n-1) :=
sorry
-- </vc-theorems>