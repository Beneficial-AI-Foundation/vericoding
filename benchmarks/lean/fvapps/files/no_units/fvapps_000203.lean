-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def largest_number (l : List Nat) : String := sorry

theorem empty_list_returns_zero :
  largest_number [] = "0" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem singleton_zero_returns_zero :
  largest_number [0] = "0" := sorry

theorem two_zeros_returns_zero :
  largest_number [0, 0] = "0" := sorry

theorem ten_and_two_returns_210 :
  largest_number [10, 2] = "210" := sorry

theorem multiple_numbers_returns_largest_possible :
  largest_number [3, 30, 34, 5, 9] = "9534330" := sorry
-- </vc-theorems>