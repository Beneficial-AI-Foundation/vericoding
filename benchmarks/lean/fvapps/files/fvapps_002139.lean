-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def winner_game (n : Nat) (edges : List (Nat × Nat × Char)) : List (List Char) :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem winner_game_correct_dimensions {n : Nat} (h: n ≥ 1) (edges : List (Nat × Nat × Char)) :
  let result := winner_game n edges
  ∀ row, row ∈ result →
    row.length = n ∧ result.length = n :=
sorry

theorem winner_game_valid_chars {n : Nat} (h1: n ≥ 2) (edges : List (Nat × Nat × Char)) :
  let result := winner_game n edges
  ∀ row, row ∈ result →  
  ∀ c, c ∈ row →
    c = 'A' ∨ c = 'B' :=
sorry

theorem winner_game_bottom_right {n : Nat} (h1: n ≥ 2) (edges : List (Nat × Nat × Char)) :
  let result := winner_game n edges
  result.getLast?.getD [] |>.getLast?.getD ' ' = 'B' :=
sorry

theorem winner_game_empty_graph :
  winner_game 1 [] = [['B']] :=
sorry
-- </vc-theorems>