-- <vc-helpers>
-- </vc-helpers>

def find_winner (players : List (String × Int)) : String := sorry

theorem identical_scores_no_winner {n : Nat} {score : Int} (h : n ≥ 2) : 
  let players := List.map (fun i => (s!"player{i}", score)) (List.range n)
  find_winner players = "Nobody wins."
  := sorry

theorem single_player_wins (name : String) (score : Int) : 
  find_winner [(name, score)] = name
  := sorry

theorem winner_is_valid (players : List (String × Int)) :
  let result := find_winner players
  let player_names := List.map Prod.fst players
  result = "Nobody wins." ∨ result ∈ player_names
  := sorry

/-
info: 'Lucy'
-/
-- #guard_msgs in
-- #eval find_winner [("Kouta", 1), ("Yuka", 1), ("Mayu", 3), ("Lucy", 2), ("Nana", 5)]

/-
info: 'Nobody wins.'
-/
-- #guard_msgs in
-- #eval find_winner [("Lucy", 2), ("Nana", 2)]

/-
info: 'Bob'
-/
-- #guard_msgs in
-- #eval find_winner [("Bob", 1), ("Alice", 2), ("Eve", 3), ("Carol", 2)]

-- Apps difficulty: interview
-- Assurance level: unguarded