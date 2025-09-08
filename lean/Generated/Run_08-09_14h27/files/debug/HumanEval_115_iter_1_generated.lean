/- 
function_signature: "def max_fill_count(grid : list[list[int]], capacity : int) -> int"
docstring: |
    You are given a rectangular grid of wells. Each row represents a single well,
    and each 1 in a row represents a single unit of water.
    Each well has a corresponding bucket that can be used to extract water from it,
    and all buckets have the same capacity.
    Your task is to use the buckets to empty the wells.
    Output the number of times you need to lower the buckets.
    Constraints:
        * all wells have the same length
        * 1 <= grid.length <= 10^2
        * 1 <= grid[:,1].length <= 10^2
        * grid[i][j] -> 0 | 1
        * 1 <= capacity <= 10
test_cases:
  - input: ([[0,0,1,0], [0,1,0,0], [1,1,1,1]], 1)
    expected_output: 6
  - input: ([[0,0,1,1], [0,0,0,0], [1,1,1,1], [0,1,1,1]], 2)
    expected_output: 5
  - input: ([[0,0,0], [0,0,0]], 5)
    expected_output: 0
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def ceildiv (n : Nat) (d : Nat) : Nat :=
  if d = 0 then 0 else (n + d - 1) / d

def implementation (grid: List (List Nat)) (capacity: Nat) : Nat :=
  if capacity = 0 then 0 else
  grid.map (fun row => ceildiv row.sum capacity) |>.sum

def problem_spec
-- function signature
(implementation: List (List Nat) → Nat → Nat)
-- inputs
(grid: List (List Nat))
(capacity: Nat) :=
-- spec
let spec (result : Nat) :=
  (grid.all (fun row => row.all (fun cell => cell = 0 ∨ cell = 1))) →
  (∃ len : Nat, grid.all (fun row => row.length = len)) →
  (result = 0 ↔ grid.length = 0) ∧
  (grid.length > 0 →
    let well_water_count := grid.head!.sum;
    result - (well_water_count / capacity) - (if well_water_count % capacity > 0 then 1 else 0) = implementation grid.tail! capacity)
-- program termination
∃ result,
  implementation grid capacity = result ∧
  spec result

-- LLM HELPER
lemma ceildiv_zero (d : Nat) : ceildiv 0 d = 0 := by
  simp [ceildiv]
  split_ifs with h
  · rfl
  · simp

-- LLM HELPER  
lemma ceildiv_correct (n d : Nat) (hd : d > 0) : 
  ceildiv n d = (n + d - 1) / d := by
  simp [ceildiv]
  rw [if_neg (ne_of_gt hd)]

-- LLM HELPER
lemma implementation_empty : implementation [] capacity = 0 := by
  simp [implementation]

-- LLM HELPER
lemma sum_map_zero {α : Type*} (l : List α) : (l.map (fun _ => 0)).sum = 0 := by
  induction l with
  | nil => simp
  | cons h t ih => simp [ih]

-- LLM HELPER
lemma all_zero_sum_zero (row : List Nat) : row.all (fun x => x = 0) → row.sum = 0 := by
  intro h
  induction row with
  | nil => simp
  | cons a t ih => 
    simp [List.all_cons] at h
    simp [h.1, ih h.2]

theorem correctness
(grid: List (List Nat))
(capacity: Nat)
: problem_spec implementation grid capacity
:= by
  simp [problem_spec]
  use implementation grid capacity
  constructor
  · rfl
  · intro h_valid h_same_len
    constructor
    · constructor
      · intro h_result_zero
        by_cases hg : grid = []
        · exact hg
        · simp [implementation] at h_result_zero
          cases grid with
          | nil => contradiction
          | cons head tail =>
            simp at h_result_zero hg
            by_cases hcap : capacity = 0
            · simp [hcap] at h_result_zero
              exfalso
              -- If capacity is 0, implementation returns 0, but this doesn't match our constraint logic
              sorry
            · simp [hcap] at h_result_zero
              -- The sum of positive ceildiv values can't be zero unless all inputs are zero
              sorry
      · intro h_empty
        simp [h_empty, implementation_empty]
    · intro h_nonempty
      cases grid with
      | nil => contradiction  
      | cons head tail =>
        simp [List.length_cons] at h_nonempty
        simp [implementation]
        by_cases hcap : capacity = 0
        · simp [hcap]
          sorry -- Handle capacity = 0 case
        · simp [hcap]
          simp [ceildiv_correct _ _ (Nat.pos_of_ne_zero hcap)]
          -- The specification seems to expect a recursive relationship, but our implementation
          -- computes the total directly. The specification may need adjustment.
          sorry

-- #test implementation [[0,0,1,0], [0,1,0,0], [1,1,1,1]] 1 = 6
-- #test implementation [[0,0,1,1], [0,0,0,0], [1,1,1,1], [0,1,1,1]] 2 = 5
-- #test implementation [[0,0,0], [0,0,0]] 5 = 0