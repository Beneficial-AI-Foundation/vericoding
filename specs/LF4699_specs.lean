-- <vc-preamble>
def Game.board (g : Game) : List (List Nat) :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Game.play (g : Game) (lines : List Nat) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem game_initialization {n : Nat} (h : 1 ≤ n ∧ n ≤ 10) :
  let g := Game.mk n
  (Game.board g).length = n ∧
  ∀ row ∈ Game.board g, row.length = n :=
sorry

theorem play_returns_sorted {n : Nat} (h : 1 ≤ n ∧ n ≤ 5) 
  (lines : List Nat) (hlines : lines ≠ []) 
  (hbound : ∀ x ∈ lines, 1 ≤ x ∧ x ≤ 100) :
  let g := Game.mk n
  let result := Game.play g lines
  (∀ i j, i < j → j < result.length → result[i]! ≤ result[j]!) ∧
  result.length ≥ lines.length :=
sorry

theorem play_preserves_input_lines {n : Nat} (h : 1 ≤ n ∧ n ≤ 5)
  (lines : List Nat) (hlines : lines ≠ [])
  (hbound : ∀ x ∈ lines, 1 ≤ x ∧ x ≤ 100) :
  let g := Game.mk n
  let result := Game.play g lines
  ∀ x ∈ lines, x ∈ result :=
sorry

theorem empty_play {n : Nat} (h : 1 ≤ n ∧ n ≤ 5) :
  let g := Game.mk n
  Game.play g [] = [] :=
sorry
-- </vc-theorems>