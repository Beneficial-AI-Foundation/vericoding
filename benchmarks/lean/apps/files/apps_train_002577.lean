-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def scrabble_score : String → Nat 
  | _ => sorry
-- </vc-definitions>

-- <vc-theorems>
theorem scrabble_score_nonnegative (word : String) : 
  scrabble_score word ≥ 0 := sorry

theorem scrabble_score_case_insensitive (word : String) :
  scrabble_score (word.toLower) = scrabble_score (word.toUpper) := sorry

theorem scrabble_score_sum_individual (word : String) :
  word ≠ "" →
  scrabble_score word = word.data.foldl (fun acc c => acc + scrabble_score s!"{c}") 0 := sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval scrabble_score ""

/-
info: 6
-/
-- #guard_msgs in
-- #eval scrabble_score "street"

/-
info: 14
-/
-- #guard_msgs in
-- #eval scrabble_score "cabbage"

/-
info: 6
-/
-- #guard_msgs in
-- #eval scrabble_score "STREET"

/-
info: 6
-/
-- #guard_msgs in
-- #eval scrabble_score "st re et"

/-
info: 22
-/
-- #guard_msgs in
-- #eval scrabble_score "quirky"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible