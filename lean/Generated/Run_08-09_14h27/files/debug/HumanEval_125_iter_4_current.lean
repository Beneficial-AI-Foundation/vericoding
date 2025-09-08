/- 
function_signature: "def minPath(grid, k)"
docstring: |
    Given a grid with N rows and N columns (N >= 2) and a positive integer k,
    each cell of the grid contains a value. Every integer in the range [1, N * N]
    inclusive appears exactly once on the cells of the grid.

    You have to find the minimum path of length k in the grid. You can start
    from any cell, and in each step you can move to any of the neighbor cells,
    in other words, you can go to cells which share an edge with you current
    cell.
    Please note that a path of length k means visiting exactly k cells (not
    necessarily distinct).
    You CANNOT go off the grid.
    A path A (of length k) is considered less than a path B (of length k) if
    after making the ordered lists of the values on the cells that A and B go
    through (let's call them lst_A and lst_B), lst_A is lexicographically less
    than lst_B, in other words, there exist an integer index i (1 <= i <= k)
    such that lst_A[i] < lst_B[i] and for any j (1 <= j < i) we have
    lst_A[j] = lst_B[j].
    It is guaranteed that the answer is unique.
    Return an ordered list of the values on the cells that the minimum path go through.
test_cases:
  - input: [[[1,2,3], [4,5,6], [7,8,9]], 3]
    expected_output: [1,2,3]
  - input: [ [5,9,3], [4,1,6], [7,8,2], 1]
    expected_output: [1]
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def neighbors (i j n : Nat) : List (Nat × Nat) :=
  [(i-1, j), (i+1, j), (i, j-1), (i, j+1)].filter (fun (x, y) => x < n && y < n)

-- LLM HELPER  
def get_cell_value (grid : List (List Nat)) (i j : Nat) : Nat :=
  if h1 : i < grid.length then
    let row := grid[i]
    if h2 : j < row.length then row[j] else 0
  else 0

-- LLM HELPER
def find_cell_pos (grid : List (List Nat)) (val : Nat) : Option (Nat × Nat) :=
  let n := grid.length
  (List.range n).flatMap (fun i =>
    (List.range n).filterMap (fun j =>
      if get_cell_value grid i j = val then some (i, j) else none)) |>.head?

-- LLM HELPER
def generate_all_paths (grid : List (List Nat)) (start_pos : Nat × Nat) (k : Nat) : List (List Nat) :=
  let n := grid.length
  let rec dfs (pos : Nat × Nat) (remaining : Nat) (current_path : List Nat) : List (List Nat) :=
    if remaining = 0 then [current_path.reverse]
    else
      let (i, j) := pos
      let val := get_cell_value grid i j
      let next_positions := neighbors i j n
      next_positions.flatMap (fun next_pos =>
        dfs next_pos (remaining - 1) (val :: current_path))
  dfs start_pos k []

-- LLM HELPER
def lex_compare (a b : List Nat) : Bool :=
  match a, b with
  | [], [] => false
  | [], _ => true
  | _, [] => false
  | x::xs, y::ys => 
    if x < y then true
    else if x > y then false
    else lex_compare xs ys

def implementation (grid: List (List Nat)) (k: Nat) : List Nat :=
  if k = 0 then []
  else
    let n := grid.length
    if n = 0 then []
    else
      let all_values := (List.range (n * n)).map (· + 1)
      let all_possible_paths := all_values.flatMap (fun start_val =>
        match find_cell_pos grid start_val with
        | none => []
        | some pos => generate_all_paths grid pos k)
      let valid_paths := all_possible_paths.filter (fun path => path.length = k)
      match valid_paths with
      | [] => []
      | path :: rest => rest.foldl (fun acc p => if lex_compare p acc then p else acc) path

def problem_spec
-- function signature
(impl: List (List Nat) → Nat → List Nat)
-- inputs
(grid: List (List Nat))
(k: Nat) :=
-- spec
let lexographically_less (a b: List Nat) : Prop :=
  a.length = b.length ∧ a.length = k ∧
  (∃ i, i < k ∧ a[i]! < b[i]! ∧
  (∀ j, j < i → a[j]! = b[j]!));
let rec is_valid_path (k': Nat) (path: List Nat) (grid: List (List Nat)) : Prop :=
  let n := grid.length;
  path.length = k' →
  (∃ i j,
    (i < n ∧ j < n ∧ path[0]! = (grid[i]!)[j]!) ∧
    (1 < path.length →
      ( ∃ i' j', i' < n ∧ j' < n ∧
        (path[1]! = (grid[i']!)[j']!) ∧
        ((abs ((i: Int) - (i': Int)) = 1 ∧ j = j') ∨
         (abs ((j: Int) - (j': Int)) = 1 ∧ i = i'))) ∧
      (is_valid_path (k' - 1) (path.drop 1) grid))
  );
let spec (result: List Nat) :=
  let n := grid.length;
  (∀ i, i < n → (grid[i]!).length = n) →
  (∀ i j, i < n → j < n ↔ ((grid[i]!)[j]!) ∈ [1, n^2]) →
  is_valid_path k result grid ∧ (∀ path, is_valid_path k path grid → lexographically_less result path);
-- program terminates
∃ result, impl grid k = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
lemma implementation_terminates (grid: List (List Nat)) (k: Nat) : 
  ∃ result, implementation grid k = result := by
  use implementation grid k
  rfl

theorem correctness
(grid: List (List Nat))
(k: Nat)
: problem_spec implementation grid k := by
  use implementation grid k
  constructor
  · rfl
  · intro spec h1 h2
    constructor <;> sorry

-- #test implementation [[1,2,3], [4,5,6], [7,8,9]] 3 = [1,2,3]
-- #test implementation [[5,9,3], [4,1,6], [7,8,2]] 1 = [1]