-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_nth_number (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_nth_number_positive (n : Nat) (h : n > 0) :
  find_nth_number n > 0 :=
sorry

theorem sequence_initial_pattern :
  find_nth_number 1 = 1 ∧
  find_nth_number 2 = 6 ∧
  find_nth_number 3 = 7 ∧
  find_nth_number 4 = 36 ∧
  find_nth_number 5 = 37 :=
sorry

theorem odd_index_increment (n : Nat) (h1 : n > 3) (h2 : n % 2 = 1) :
  find_nth_number n = find_nth_number (n-1) + 1 :=
sorry
-- </vc-theorems>