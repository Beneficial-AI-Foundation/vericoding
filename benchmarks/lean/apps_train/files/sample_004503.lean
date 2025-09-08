/-
Let's just place tokens on a connect four board.

** INPUT **

Provided as input the list of columns where a token is placed, from 0 to 6 included.
The first player starting is the yellow one (marked with `Y`), then the red (marked with `R`); the other cells might be empty and marked with `-`.

** OUTPUT **

The output is the state of the board after all the tokens in input have been placed.

** ASSUMPTIONS **

- The board is the standard 7x6;
- Of course you'll need to deal with gravity;
- You don't need to hassle with wrong input, wrong column numbers, checking for full column or going off the board;
- the columns list will always include proper column numbers;
- Notice: when you read the results in tests, the highest row appears first and the lowest row appears last; debugging using `\n` after each row might help (check example);

** EXAMPLES **

1.
```
Moves = [0,1,2,5,6]

Result:
['-', '-', '-', '-', '-', '-', '-']
['-', '-', '-', '-', '-', '-', '-']
['-', '-', '-', '-', '-', '-', '-']
['-', '-', '-', '-', '-', '-', '-']
['-', '-', '-', '-', '-', '-', '-']
['Y', 'R', 'Y', '-', '-', 'R', 'Y']
```
2.
```
Moves = [0,1,2,5,6,2,0,0]

Result:
['-', '-', '-', '-', '-', '-', '-']
['-', '-', '-', '-', '-', '-', '-']
['-', '-', '-', '-', '-', '-', '-']
['R', '-', '-', '-', '-', '-', '-']
['Y', '-', 'R', '-', '-', '-', '-']
['Y', 'R', 'Y', '-', '-', 'R', 'Y']
```

See test cases for better details.
-/

def Board := List (List Cell)

def connect_four_place (moves: List Nat) : Board :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def countCells (b: Board) (p: Cell → Bool) : Nat :=
  b.join.foldl (fun acc c => if p c then acc + 1 else acc) 0

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

-- Apps difficulty: introductory
-- Assurance level: guarded