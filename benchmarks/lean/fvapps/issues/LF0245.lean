-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def numMagicSquaresInside (grid : List (List Int)) : Int := sorry
def isMagicSquare (square : List (List Int)) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem numMagicSquaresInside_small_grid
  (grid : List (List Int))
  (h1 : grid.length < 3 ∨ grid.head!.length < 3) :
  numMagicSquaresInside grid = 0 := sorry

theorem isMagicSquare_returns_bool (square : List (List Int)) :
  isMagicSquare square = true ∨ isMagicSquare square = false := sorry

theorem isMagicSquare_invalid_range
  (square : List (List Int))
  (h1 : ∃ x, x ∈ square.join ∧ (x > 9 ∨ x < 1)) : 
  isMagicSquare square = false := sorry

theorem numMagicSquaresInside_empty_grid
  (rows cols : Nat)
  (h1 : rows ≥ 3)
  (h2 : cols ≥ 3) :
  numMagicSquaresInside (List.replicate rows (List.replicate cols 0)) ≥ 0 := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval numMagicSquaresInside [[4, 3, 8, 4], [9, 5, 1, 9], [2, 7, 6, 2]]

/-
info: 0
-/
-- #guard_msgs in
-- #eval numMagicSquaresInside [[8]]

/-
info: 0
-/
-- #guard_msgs in
-- #eval numMagicSquaresInside [[4, 7, 8], [9, 5, 1], [2, 3, 6]]
-- </vc-theorems>