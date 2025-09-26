-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def num_rook_captures (board: Board) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem rook_captures_bounds {b : List (List Char)} : 
  b.length = 8 ∧ 
  (∀ r ∈ b, r.length = 8) →
  let board := Board.mk b
  let captures := num_rook_captures board 
  0 ≤ captures ∧ captures ≤ 4 := 
  sorry

theorem rook_presence {b : List (List Char)} :
  b.length = 8 ∧
  (∀ r ∈ b, r.length = 8) →
  let board := Board.mk b
  ((b.map (fun row => row.filter (· = 'R'))).join).length = 1 :=
  sorry

theorem blocked_by_bishop {b : List (List Char)} :
  b.length = 8 ∧
  (∀ r ∈ b, r.length = 8) →
  let board := Board.mk b
  let blocked_pawns := -- count of pawns blocked by bishops
    0 -- placeholder
  num_rook_captures board ≤ 4 - blocked_pawns :=
  sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval num_rook_captures [[".", ".", ".", ".", ".", ".", ".", "."], [".", ".", ".", "p", ".", ".", ".", "."], [".", ".", ".", "R", ".", ".", ".", "p"], [".", ".", ".", ".", ".", ".", ".", "."], [".", ".", ".", ".", ".", ".", ".", "."], [".", ".", ".", "p", ".", ".", ".", "."], [".", ".", ".", ".", ".", ".", ".", "."], [".", ".", ".", ".", ".", ".", ".", "."]]

/-
info: 0
-/
-- #guard_msgs in
-- #eval num_rook_captures [[".", ".", ".", ".", ".", ".", ".", "."], [".", "p", "p", "p", "p", "p", ".", "."], [".", "p", "p", "B", "p", "p", ".", "."], [".", "p", "B", "R", "B", "p", ".", "."], [".", "p", "p", "B", "p", "p", ".", "."], [".", "p", "p", "p", "p", "p", ".", "."], [".", ".", ".", ".", ".", ".", ".", "."], [".", ".", ".", ".", ".", ".", ".", "."]]
-- </vc-theorems>