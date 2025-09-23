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
-- </vc-theorems>