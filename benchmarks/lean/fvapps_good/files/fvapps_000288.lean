-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isSelfCrossing (moves : List Int) : Bool := sorry

theorem short_sequences_never_cross (moves: List Int)
  (h: moves.length < 4)
  (h_nonneg : ∀ x ∈ moves, x ≥ 0) :
  ¬(isSelfCrossing moves) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem equal_square_forms_crossing (moves: List Int)
  (h_len: moves.length = 4)
  (h_pos: ∀ x ∈ moves, x > 0)
  (h_equal: ∀ i j, i < moves.length → j < moves.length → moves[i]! = moves[j]!) :
  isSelfCrossing moves := sorry

theorem growing_spiral_never_crosses (moves: List Int)
  (h_len: moves.length = 4)
  (h_pos: ∀ x ∈ moves, x > 0)
  (h_increasing: ∀ i, i + 1 < moves.length → moves[i]! < moves[i+1]!) :
  ¬(isSelfCrossing moves) := sorry

theorem negative_moves_invalid (moves: List Int)
  (h: ∃ x ∈ moves, x < 0) :
  isSelfCrossing moves = false := sorry

theorem delayed_crossing_occurs (moves: List Int)
  (h_len: moves.length = 6)
  (h_nonneg: ∀ x ∈ moves, x ≥ 0)
  (h_cross: moves[5]! ≥ moves[3]! ∧ moves[4]! = moves[2]!) :
  isSelfCrossing moves := sorry
-- </vc-theorems>