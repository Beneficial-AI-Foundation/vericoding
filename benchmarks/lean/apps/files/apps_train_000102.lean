/-
Ashish and Vivek play a game on a matrix consisting of $n$ rows and $m$ columns, where they take turns claiming cells. Unclaimed cells are represented by $0$, while claimed cells are represented by $1$. The initial state of the matrix is given. There can be some claimed cells in the initial state.

In each turn, a player must claim a cell. A cell may be claimed if it is unclaimed and does not share a row or column with any other already claimed cells. When a player is unable to make a move, he loses and the game ends.

If Ashish and Vivek take turns to move and Ashish goes first, determine the winner of the game if both of them are playing optimally.

Optimal play between two players means that both players choose the best possible strategy to achieve the best possible outcome for themselves.

-----Input-----

The first line consists of a single integer $t$ $(1 \le t \le 50)$ — the number of test cases. The description of the test cases follows.

The first line of each test case consists of two space-separated integers $n$, $m$ $(1 \le n, m \le 50)$ — the number of rows and columns in the matrix.

The following $n$ lines consist of $m$ integers each, the $j$-th integer on the $i$-th line denoting $a_{i,j}$ $(a_{i,j} \in \{0, 1\})$.

-----Output-----

For each test case if Ashish wins the game print "Ashish" otherwise print "Vivek" (without quotes).

-----Example-----
Input
4
2 2
0 0
0 0
2 2
0 0
0 1
2 3
1 0 1
1 1 0
3 3
1 0 0
0 0 0
1 0 0

Output
Vivek
Ashish
Vivek
Ashish

-----Note-----

For the first case: One possible scenario could be: Ashish claims cell $(1, 1)$, Vivek then claims cell $(2, 2)$. Ashish can neither claim cell $(1, 2)$, nor cell $(2, 1)$ as cells $(1, 1)$ and $(2, 2)$ are already claimed. Thus Ashish loses. It can be shown that no matter what Ashish plays in this case, Vivek will win. 

For the second case: Ashish claims cell $(1, 1)$, the only cell that can be claimed in the first move. After that Vivek has no moves left.

For the third case: Ashish cannot make a move, so Vivek wins.

For the fourth case: If Ashish claims cell $(2, 3)$, Vivek will have no moves left.
-/

def solve_game (n m : Nat) (grid : List (List Nat)) : String :=
  sorry

def countEmptyRows (grid : List (List Nat)) : Nat :=
  (grid.filter (fun row => row.all (fun x => x = 0))).length

-- <vc-helpers>
-- </vc-helpers>

def countEmptyCols (n m : Nat) (grid : List (List Nat)) : Nat :=
  let isEmptyCol (j : Nat) := (List.range n).all (fun i => 
    match grid.get? i with
    | none => true
    | some row => match row.get? j with
      | none => true
      | some x => x = 0)
  (List.range m).filter isEmptyCol |>.length

theorem solve_game_returns_valid_winner (n m : Nat) (grid : List (List Nat))
  (h1 : n > 0) (h2 : m > 0) (h3 : grid.length = n)
  (h4 : ∀ row ∈ grid, row.length = m)
  (h5 : ∀ row ∈ grid, ∀ x ∈ row, x = 0 ∨ x = 1) :
  solve_game n m grid = "Ashish" ∨ solve_game n m grid = "Vivek" :=
sorry

theorem winner_depends_on_empty_lines (n m : Nat) (grid : List (List Nat))
  (h1 : n > 0) (h2 : m > 0) (h3 : grid.length = n)
  (h4 : ∀ row ∈ grid, row.length = m)
  (h5 : ∀ row ∈ grid, ∀ x ∈ row, x = 0 ∨ x = 1) :
  let empty_rows := countEmptyRows grid
  let empty_cols := countEmptyCols n m grid
  let min_empty := min empty_rows empty_cols
  solve_game n m grid = "Ashish" ↔ min_empty % 2 = 1 :=
sorry

theorem all_zeros_grid (n m : Nat) (h1 : n > 0) (h2 : m > 0) :
  let grid := List.replicate n (List.replicate m 0)
  solve_game n m grid = (if min n m % 2 = 1 then "Ashish" else "Vivek") :=
sorry

theorem no_empty_lines (n m : Nat) (h1 : n > 0) (h2 : m > 0) :
  let grid := List.replicate n (List.replicate m 1)
  solve_game n m grid = "Vivek" :=
sorry

/-
info: 'Vivek'
-/
-- #guard_msgs in
-- #eval solve_game 2 2 [[0, 0], [0, 0]]

/-
info: 'Ashish'
-/
-- #guard_msgs in
-- #eval solve_game 2 2 [[0, 0], [0, 1]]

/-
info: 'Vivek'
-/
-- #guard_msgs in
-- #eval solve_game 2 3 [[1, 0, 1], [1, 1, 0]]

-- Apps difficulty: interview
-- Assurance level: unguarded