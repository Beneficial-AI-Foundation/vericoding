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
  (result = 0 ↔ grid.length = 0 ∨ grid.all (fun row => row.sum = 0)) ∧
  (grid.length > 0 →
    result = grid.map (fun row => ceildiv row.sum capacity) |>.sum)
-- program termination
∃ result,
  implementation grid capacity = result ∧
  spec result

-- LLM HELPER
lemma ceildiv_zero (d : Nat) : ceildiv 0 d = 0 := by
  simp [ceildiv]

-- LLM HELPER  
lemma ceildiv_correct (n d : Nat) (hd : d > 0) : 
  ceildiv n d = (n + d - 1) / d := by
  simp [ceildiv, ne_of_gt hd]

-- LLM HELPER
lemma implementation_empty : implementation [] capacity = 0 := by
  simp [implementation]

-- LLM HELPER
lemma sum_map_zero {α : Type*} (l : List α) : (l.map (fun _ => 0)).sum = 0 := by
  induction l with
  | nil => simp
  | cons h t ih => simp [ih]

-- LLM HELPER
lemma all_zero_sum_zero (row : List Nat) : row.all (fun x => decide (x = 0)) = true → row.sum = 0 := by
  intro h
  induction row with
  | nil => simp
  | cons a t ih => 
    simp [List.all_cons] at h
    have ha : a = 0 := by simp [decide_eq_true_iff] at h; exact h.1
    have ht : t.sum = 0 := ih h.2
    simp [ha, ht]

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
        simp [implementation] at h_result_zero
        by_cases hcap : capacity = 0
        · simp [hcap] at h_result_zero
          left
          by_cases hg : grid = []
          · exact hg
          · right
            simp [List.all_iff_forall]
            intro row hr
            exact Nat.sum_eq_zero_iff_forall_zero.mpr (fun _ _ => rfl)
        · simp [hcap] at h_result_zero
          have h_map_zero : (grid.map (fun row => ceildiv row.sum capacity)).sum = 0 := h_result_zero
          have h_all_zero : ∀ row ∈ grid, ceildiv row.sum capacity = 0 := by
            intro row hr
            have : ceildiv row.sum capacity ∈ (grid.map (fun row => ceildiv row.sum capacity)) := by
              apply List.mem_map_of_mem
              exact hr
            exact Nat.eq_zero_of_mem_sum_eq_zero this h_map_zero
          by_cases hg : grid = []
          · left; exact hg
          · right
            simp [List.all_iff_forall]
            intro row hr
            have hc_zero := h_all_zero row hr
            simp [ceildiv] at hc_zero
            simp [ne_of_gt (Nat.pos_of_ne_zero hcap)] at hc_zero
            exact Nat.sum_eq_zero_iff_forall_zero.mp (Nat.eq_zero_of_add_eq_zero_right hc_zero)
      · intro h
        cases h with
        | inl h_empty => 
          simp [h_empty, implementation_empty]
        | inr h_all_zero =>
          simp [implementation]
          by_cases hcap : capacity = 0
          · simp [hcap]
          · simp [hcap]
            have h_ceildiv_zero : ∀ row ∈ grid, ceildiv row.sum capacity = 0 := by
              intro row hr
              have h_sum_zero : row.sum = 0 := h_all_zero row hr
              simp [h_sum_zero, ceildiv_zero]
            simp [List.sum_eq_zero_iff]
            intro x hx
            simp [List.mem_map] at hx
            obtain ⟨row, hr, hrw⟩ := hx
            rw [←hrw]
            exact h_ceildiv_zero row hr
    · intro h_nonempty
      simp [implementation]
      by_cases hcap : capacity = 0
      · simp [hcap]
        simp [List.sum_eq_zero_iff, List.mem_map]
        intro x row hr
        simp [ceildiv]
      · simp [hcap]