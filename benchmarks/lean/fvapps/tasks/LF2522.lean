-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def bingo (numbers : List Int) : String := sorry

theorem bingo_returns_valid_string (numbers : List Int) :
  numbers ≠ [] →
  (bingo numbers = "WIN" ∨ bingo numbers = "LOSE") := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem bingo_win_condition_with_bingo_numbers
  (numbers : List Int)
  (h : ∀ n ∈ numbers, 1 ≤ n ∧ n ≤ 30) :
  let bingo_numbers := [2, 9, 14, 7, 15]
  bingo (numbers ++ bingo_numbers) = "WIN" := sorry

theorem bingo_win_condition_monotone
  (numbers extra_numbers : List Int) :
  bingo numbers = "WIN" →
  bingo (numbers ++ extra_numbers) = "WIN" := sorry

theorem bingo_missing_required_loses
  (numbers : List Int)
  (h : ∀ n ∈ numbers, n ≠ 2 ∧ n ≠ 9 ∧ n ≠ 14 ∧ n ≠ 7 ∧ n ≠ 15) :
  bingo numbers = "LOSE" := sorry
-- </vc-theorems>