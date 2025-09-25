-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count (board : List (List Int)) : List SquareCount := sorry

theorem count_square_ones_board 
  {n : Nat} (h : n ≥ 2)
  (board : List (List Int))
  (h_board : board.length = n ∧ ∀ row ∈ board, row.length = n)
  (h_ones : ∀ i j, i < n → j < n → board[i]![j]! = 1) :
  ∀ size, 2 ≤ size → size ≤ n → 
    let result := count board
    ∃ sc ∈ result, sc.size = size ∧ sc.count = (n - size + 1) ^ 2 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_preserves_input
  {rows cols : Nat} (h : rows ≥ 1 ∧ cols ≥ 1)
  (board : List (List Int)) 
  (h_board : board.length = rows ∧ ∀ row ∈ board, row.length = cols) :
  let board' := board
  count board = count board' ∧ board = board' := sorry

/-
info: {2: 1}
-/
-- #guard_msgs in
-- #eval count [[1, 1], [1, 1]]

/-
info: {2: 4, 3: 1}
-/
-- #guard_msgs in
-- #eval count [[1, 1, 1], [1, 1, 1], [1, 1, 1]]

/-
info: {}
-/
-- #guard_msgs in
-- #eval count [[1, 1, 1], [1, 0, 1], [1, 1, 1]]
-- </vc-theorems>