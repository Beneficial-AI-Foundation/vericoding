-- <vc-preamble>
def check (p1 p2: (Nat × Nat)) : Bool := sorry

def passAll (xs: List (Nat × Nat)) (q: Nat × Nat) : Bool := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def reconstruct (points: List Nat) (n: Nat) : List (List String) := sorry 

def solveNQueens (n: Nat) : List (List (List String)) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem check_symmetry (p1 p2: (Nat × Nat)) :
  check p1 p2 = check p2 p1 := sorry

theorem check_self_conflict (p: (Nat × Nat)) : 
  check p p = true := sorry

theorem solutions_valid_size (n: Nat) (h: 0 < n ∧ n ≤ 8) :
  ∀ board ∈ solveNQueens n,
    (board.length = n ∧ 
     ∀ row ∈ board, row.length = n ∧
     List.length (List.join (board.map (λ row => row.filter (· = "Q")))) = n) := sorry

theorem queens_dont_conflict (n: Nat) (h: 0 < n ∧ n ≤ 8) :
  ∀ board ∈ solveNQueens n,
    let queens := (List.range n).filterMap (λ i => 
      let row := board[i]!
      row.findIdx? (· = "Q") |>.map (λ j => (i, j)))
    ∀ i j, i < queens.length → j < queens.length → i ≠ j →
      ¬check queens[i]! queens[j]! := sorry

theorem reconstruct_dimensions (n: Nat) :
  let points := List.range n
  let board := reconstruct points n
  board.length = n ∧ ∀ row ∈ board, row.length = n := sorry

theorem handle_nonpositive_size :
  solveNQueens 0 = [] := sorry

/-
info: [['Q']]
-/
-- #guard_msgs in
-- #eval solveNQueens 1

/-
info: expected
-/
-- #guard_msgs in
-- #eval solveNQueens 4

/-
info: []
-/
-- #guard_msgs in
-- #eval solveNQueens 2
-- </vc-theorems>