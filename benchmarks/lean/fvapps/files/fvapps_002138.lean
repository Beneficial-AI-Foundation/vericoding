-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_max_popcount (l r : Nat) : Nat :=
  sorry

def popcount (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem output_in_range (l r : Nat) :
  let ordered_l := min l r
  let ordered_r := max l r
  let result := get_max_popcount ordered_l ordered_r
  ordered_l ≤ result ∧ result ≤ ordered_r :=
sorry

theorem same_number (x : Nat) :
  get_max_popcount x x = x :=
sorry

theorem consecutive_numbers (x : Nat) :
  popcount (get_max_popcount x (x + 1)) ≥ popcount x :=
sorry
-- </vc-theorems>