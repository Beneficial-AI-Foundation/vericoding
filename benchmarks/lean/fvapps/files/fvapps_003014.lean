-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def parse_fen (fen: String) : String := sorry 

theorem empty_board_dimensions {turn : Char} (h: turn = 'w' ∨ turn = 'b'):
  let result := parse_fen s!"8/8/8/8/8/8/8/8 {turn} - -"
  let lines := result.splitOn "\n"
  lines.length = 9 ∧ 
  (∀ l ∈ lines.take 8, l.length = 8) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem board_pattern_alternates:
  let result := parse_fen "8/8/8/8/8/8/8/8 w - -"
  let lines := (result.splitOn "\n").take 8
  ∀ i j, i < 8 ∧ j < 8 → 
    (((i + j).mod 2 = 0) → lines[i]!.data[j]! = '▇') ∧
    (((i + j).mod 2 ≠ 0) → lines[i]!.data[j]! = '＿') := sorry

theorem different_turn_perspectives_differ:
  parse_fen "k7/8/8/8/8/8/8/K7 w - -" ≠ 
  parse_fen "k7/8/8/8/8/8/K7 b - -" := sorry

theorem piece_representation_correct:
  let result := parse_fen "k7/8/8/8/8/8/8/K7 w - -"
  let lines := (result.splitOn "\n").take 8
  ('♔' ∈ lines[0]!.data) ∧ 
  ('♚' ∈ lines[7]!.data) := sorry
-- </vc-theorems>