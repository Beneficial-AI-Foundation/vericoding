-- <vc-preamble>
def Board := List (List Cell)

def connect_four_place (moves: List Nat) : Board :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def countCells (b: Board) (p: Cell → Bool) : Nat :=
  b.join.foldl (fun acc c => if p c then acc + 1 else acc) 0
-- </vc-definitions>

-- <vc-theorems>
theorem board_dimensions {moves : List Nat} 
  (h : ∀ m ∈ moves, m ≤ 6) : 
  let board := connect_four_place moves
  board.length = 6 ∧ List.all board (fun row => row.length = 7) :=
sorry

theorem alternating_players {moves : List Nat}
  (h : ∀ m ∈ moves, m ≤ 6) :
  let board := connect_four_place moves
  let yellow_count := countCells board (fun c => c == Cell.Yellow)
  let red_count := countCells board (fun c => c == Cell.Red)
  yellow_count ≤ red_count + 1 ∧ red_count ≤ yellow_count + 1 :=
sorry

theorem gravity_effect {moves : List Nat}
  (h : ∀ m ∈ moves, m ≤ 6) :
  let board := connect_four_place moves
  ∀ col, col < 7 → 
  ∀ row₁ row₂, row₁ < row₂ → row₂ < 6 →
    Option.isSome ((board.get? row₂).bind (·.get? col)) →
    (board.get? row₂).bind (·.get? col) = some Cell.Empty → 
    (board.get? row₁).bind (·.get? col) = some Cell.Empty :=
sorry

theorem valid_pieces {moves : List Nat}
  (h : ∀ m ∈ moves, m ≤ 6) :
  let board := connect_four_place moves
  board.join.all (fun cell => 
    cell == Cell.Empty || cell == Cell.Yellow || cell == Cell.Red) :=
sorry

theorem empty_board :
  connect_four_place [] = 
    List.replicate 6 (List.replicate 7 Cell.Empty) :=
sorry
-- </vc-theorems>