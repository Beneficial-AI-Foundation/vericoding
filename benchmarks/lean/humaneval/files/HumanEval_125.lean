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

import Imports.AllImports

-- <vc-helpers>
-- </vc-helpers>

def implementation (grid: List (List Nat)) (k: Nat) : List Nat :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(impl: List (List Nat) → Nat → List Nat)
-- inputs
(grid: List (List Nat))
(k: Nat) :=
-- spec
let lexographically_less (a b: List Nat) : Prop :=
  a.length = b.length ∧ a.length = k ∧
  (∃ i, i < k ∧ a.get! i < b.get! i ∧
  (∀ j, j < i → a.get! j = b.get! j));
let rec is_valid_path (k': Nat) (path: List Nat) (grid: List (List Nat)) : Prop :=
  let n := grid.length;
  path.length = k' →
  (∃ i j,
    (i < n ∧ j < n ∧ path.get! 0 = (grid.get! i).get! j) ∧
    (1 < path.length →
      ( ∃ i' j', i' < n ∧ j' < n ∧
        (path.get! 1 = (grid.get! i').get! j') ∧
        ((abs ((i: Int) - (i': Int)) = 1 ∧ j = j') ∨
         (abs ((j: Int) - (j': Int)) = 1 ∧ i = i'))) ∧
      (is_valid_path (k' - 1) (path.drop 1) grid))
  );
let spec (result: List Nat) :=
  let n := grid.length;
  (∀ i, i < n → (grid.get! i).length = n) →
  (∀ i j, i < n → j < n ↔ ((grid.get! i).get! j) ∈ [1, n^2]) →
  is_valid_path k result grid ∧ (∀ path, is_valid_path k path grid → lexographically_less result path);
-- program terminates
∃ result, impl grid k = result ∧
-- return value satisfies spec
spec result

theorem correctness
(grid: List (List Nat))
(k: Nat)
: problem_spec implementation grid k :=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation [[1,2,3], [4,5,6], [7,8,9]] 3 = [1,2,3]
-- #test implementation [[5,9,3], [4,1,6], [7,8,2]] 1 = [1]