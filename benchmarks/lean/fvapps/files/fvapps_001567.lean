-- <vc-preamble>
def countChar (c : Char) (l : List Char) : Nat :=
  l.foldl (fun acc x => if x = c then acc + 1 else acc) 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def pawnMoveTracker (moves : List String) : List (List Char) :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_moves_initial_position (moves : List String) :
  moves = [] →
  let board := pawnMoveTracker moves
  (board.length = 8 ∧
   (∀ row ∈ board, row.length = 8) ∧
   (∀ i, i < 8 → (board.get! 1).get! i = 'p') ∧
   (∀ i, i < 8 → (board.get! 6).get! i = 'P')) :=
sorry

theorem valid_moves_invariants (moves : List String) :
  let board := pawnMoveTracker moves
  (board.length = 8 ∧
   (∀ row ∈ board, row.length = 8) ∧
   let whitePawns := (board.foldl (fun acc row => acc + countChar 'P' row) 0)
   let blackPawns := (board.foldl (fun acc row => acc + countChar 'p' row) 0)
   0 ≤ whitePawns ∧ whitePawns ≤ 8 ∧
   0 ≤ blackPawns ∧ blackPawns ≤ 8) :=
sorry

theorem valid_first_white_move (file : Char) (rank : Char) :
  file ∈ ['a', 'b', 'c', 'd', 'e', 'f', 'g', 'h'] →
  rank = '4' →
  let move := String.mk [file, rank]
  let board := pawnMoveTracker [move]
  ((board.get! 6).get! (file.toNat - 'a'.toNat) = '.' ∧
   (board.get! 4).get! (file.toNat - 'a'.toNat) = 'P') :=
sorry
-- </vc-theorems>