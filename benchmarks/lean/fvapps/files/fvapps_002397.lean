-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_nth_digit (n : Nat) : Nat := sorry

theorem find_nth_digit_in_range (n : Nat) (h : n > 0) :
  let result := find_nth_digit n
  0 ≤ result ∧ result ≤ 9 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem first_nine_digits_identity (n : Nat) (h1 : n > 0) (h2 : n ≤ 9) :
  find_nth_digit n = n := sorry

theorem digit_boundaries_valid_10 (offset : Nat) (h : offset ≤ 9) :
  let n := 10 + offset
  let result := find_nth_digit n
  0 ≤ result ∧ result ≤ 9 := sorry

theorem digit_boundaries_valid_100 (offset : Nat) (h : offset ≤ 9) : 
  let n := 100 + offset
  let result := find_nth_digit n
  0 ≤ result ∧ result ≤ 9 := sorry

theorem digit_boundaries_valid_1000 (offset : Nat) (h : offset ≤ 9) :
  let n := 1000 + offset
  let result := find_nth_digit n
  0 ≤ result ∧ result ≤ 9 := sorry

theorem find_nth_digit_deterministic (n : Nat) (h : n > 0) :
  find_nth_digit n = find_nth_digit n := sorry
-- </vc-theorems>