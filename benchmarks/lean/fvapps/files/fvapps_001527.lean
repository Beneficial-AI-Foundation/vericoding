-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_highest_digit (n : Nat) : Nat := sorry

theorem find_highest_digit_bounds (n : Nat) :
  let result := find_highest_digit n
  0 ≤ result ∧ result ≤ 9 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_digit_case (n : Nat) :
  n ≤ 9 → find_highest_digit n = n := sorry
-- </vc-theorems>