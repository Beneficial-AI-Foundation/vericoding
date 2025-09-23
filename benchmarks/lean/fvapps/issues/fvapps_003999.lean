-- <vc-preamble>
def calculateScore (initialScore: Nat) (snitch: SnitchResult) : Nat :=
  match snitch with
  | SnitchResult.Yes => initialScore + 150
  | SnitchResult.No => initialScore
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def gameWinners (gryffindor: Nat × SnitchResult) (slytherin: Nat × SnitchResult) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem game_winners_valid_output (g s: Nat × SnitchResult) : 
  let result := gameWinners g s
  result = "Gryffindor wins!" ∨ result = "Slytherin wins!" ∨ result = "It's a draw!" := by
  sorry

theorem game_winners_correct_result (g s: Nat × SnitchResult) :
  let g_score := calculateScore g.1 g.2
  let s_score := calculateScore s.1 s.2
  let result := gameWinners g s
  (result = "Gryffindor wins!" ↔ g_score > s_score) ∧
  (result = "Slytherin wins!" ↔ s_score > g_score) ∧
  (result = "It's a draw!" ↔ g_score = s_score) := by
  sorry

theorem equal_scores_no_snitch (score: Nat) :
  gameWinners (score, SnitchResult.No) (score, SnitchResult.No) = "It's a draw!" := by
  sorry

theorem only_one_snitch_possible (score: Nat) :
  gameWinners (score, SnitchResult.Yes) (score, SnitchResult.Yes) = "It's a draw!" := by
  sorry

/-
info: 'Gryffindor wins!'
-/
-- #guard_msgs in
-- #eval game_winners [100, "yes"] [100, "no"]

/-
info: 'Slytherin wins!'
-/
-- #guard_msgs in
-- #eval game_winners [350, "no"] [250, "yes"]

/-
info: "It's a draw!"
-/
-- #guard_msgs in
-- #eval game_winners [100, "yes"] [250, "no"]
-- </vc-theorems>