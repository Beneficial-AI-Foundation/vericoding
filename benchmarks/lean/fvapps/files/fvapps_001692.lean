-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_sequence_value (n : Nat) : Nat := sorry

theorem sequence_bounded (n : Nat) :
  let result := find_sequence_value n
  0 ≤ result ∧ result ≤ n := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem base_cases :
  find_sequence_value 0 = 0 ∧
  find_sequence_value 1 = 1 ∧
  find_sequence_value 2 = 2 ∧ 
  find_sequence_value 3 = 2 := sorry

theorem sequence_monotonic (n : Nat) :
  n ≥ 4 →
  find_sequence_value n ≥ find_sequence_value (n-1) := sorry
-- </vc-theorems>