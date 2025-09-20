-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_digits (n : Int) : String := sorry

theorem single_digit_count 
  (n : Int) (h : 0 ≤ n ∧ n ≤ 9) : 
  count_digits n = "1" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem double_digit_count 
  (n : Int) (h : 10 ≤ n ∧ n ≤ 99) :
  count_digits n = "2" := sorry

theorem triple_digit_count
  (n : Int) (h : 100 ≤ n ∧ n ≤ 999) :
  count_digits n = "3" := sorry

theorem more_than_three_digits
  (n : Int) (h : 1000 ≤ n) :
  count_digits n = "More than 3 digits" := sorry

theorem digit_count_ranges
  (n : Int) :
  (n < 10 → count_digits n = "1") ∧ 
  (10 ≤ n ∧ n < 100 → count_digits n = "2") ∧
  (100 ≤ n ∧ n < 1000 → count_digits n = "3") ∧
  (1000 ≤ n → count_digits n = "More than 3 digits") := sorry
-- </vc-theorems>