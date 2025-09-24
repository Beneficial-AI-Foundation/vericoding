-- <vc-preamble>
def is_vowel (c : Char) : Bool :=
  c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'

def score_from_result (result : String) : Nat :=
  if result == "Draw" then 0
  else String.toNat! (result.splitOn " " |>.get! 1)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def minion_game (s : String) : String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem minion_game_result_format (s : String) (h : s.all (fun c => c.isUpper)) :
  let result := minion_game s
  result.startsWith "Kevin " ∨ result.startsWith "Stuart " ∨ result = "Draw" :=
sorry

theorem minion_game_score_bounds (s : String) (h : s.all (fun c => c.isUpper)) :
  let result := minion_game s
  let score := score_from_result result
  result ≠ "Draw" →
  score > 0 ∧ score ≤ (s.length * (s.length + 1)) / 2 :=
sorry

theorem minion_game_scores_sum (s : String) (h : s.all (fun c => c.isUpper)) :
  let result := minion_game s
  let total := (s.length * (s.length + 1)) / 2
  result ≠ "Draw" →
  score_from_result result + (total - score_from_result result) = total :=
sorry

theorem minion_game_all_vowels (s : String)
  (h₁ : s.length > 0)
  (h₂ : s.all (fun c => is_vowel c)) :
  (minion_game s).startsWith "Kevin " :=
sorry

theorem minion_game_all_consonants (s : String)
  (h₁ : s.length > 0)
  (h₂ : s.all (fun c => c.isUpper ∧ !is_vowel c)) :
  (minion_game s).startsWith "Stuart " :=
sorry
-- </vc-theorems>