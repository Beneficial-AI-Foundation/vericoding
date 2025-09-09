-- <vc-helpers>
-- </vc-helpers>

def bingo (numbers : List Int) : String := sorry

theorem bingo_returns_valid_string (numbers : List Int) :
  numbers ≠ [] →
  (bingo numbers = "WIN" ∨ bingo numbers = "LOSE") := sorry

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

/-
info: 'LOSE'
-/
-- #guard_msgs in
-- #eval bingo [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-
info: 'LOSE'
-/
-- #guard_msgs in
-- #eval bingo [20, 12, 23, 14, 6, 22, 12, 17, 2, 26]

/-
info: 'WIN'
-/
-- #guard_msgs in
-- #eval bingo [1, 2, 3, 7, 5, 14, 7, 15, 9, 10]

-- Apps difficulty: introductory
-- Assurance level: unguarded