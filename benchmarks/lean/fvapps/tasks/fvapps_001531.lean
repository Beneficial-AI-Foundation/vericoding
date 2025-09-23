-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_winner (players : List (String × Int)) : String := sorry

theorem identical_scores_no_winner {n : Nat} {score : Int} (h : n ≥ 2) : 
  let players := List.map (fun i => (s!"player{i}", score)) (List.range n)
  find_winner players = "Nobody wins."
  := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_player_wins (name : String) (score : Int) : 
  find_winner [(name, score)] = name
  := sorry

theorem winner_is_valid (players : List (String × Int)) :
  let result := find_winner players
  let player_names := List.map Prod.fst players
  result = "Nobody wins." ∨ result ∈ player_names
  := sorry
-- </vc-theorems>