import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
(implementation: List (List Nat) → Nat → Nat)
(grid: List (List Nat))
(capacity: Nat) :=
let spec (result : Nat) :=
  (grid.all (fun row => row.all (fun cell => cell = 0 ∨ cell = 1))) →
  (∃ len : Nat, grid.all (fun row => row.length = len)) →
  (result = 0 ↔ grid.length = 0) ∧
  (grid.length > 0 →
    let well_water_count := grid.head!.sum;
    result - (well_water_count / capacity) - (if well_water_count % capacity > 0 then 1 else 0) = implementation grid.tail! capacity)
∃ result,
  implementation grid capacity = result ∧
  spec result

def implementation (grid: List (List Nat)) (capacity: Nat) : Nat := 
  match grid with
  | [] => 0
  | row :: rest => 
    let well_water_count := row.sum
    let buckets_needed := well_water_count / capacity + (if well_water_count % capacity > 0 then 1 else 0)
    buckets_needed + implementation rest capacity

-- LLM HELPER
lemma list_head_tail_decomp {α : Type*} (l : List α) (h : l.length > 0) : l = l.head! :: l.tail! := by
  cases l with
  | nil => simp at h
  | cons head tail => simp [List.head!, List.tail!]

-- LLM HELPER
lemma implementation_empty : implementation [] capacity = 0 := by
  simp [implementation]

-- LLM HELPER
lemma implementation_cons (row : List Nat) (rest : List (List Nat)) (capacity : Nat) :
  implementation (row :: rest) capacity = 
  let well_water_count := row.sum
  let buckets_needed := well_water_count / capacity + (if well_water_count % capacity > 0 then 1 else 0)
  buckets_needed + implementation rest capacity := by
  simp [implementation]

theorem correctness
(grid: List (List Nat))
(capacity: Nat)
: problem_spec implementation grid capacity := by
  simp [problem_spec]
  use implementation grid capacity
  constructor
  · rfl
  · intro h_binary h_rectangular
    constructor
    · constructor
      · intro h_result_zero
        cases grid with
        | nil => rfl
        | cons row rest => 
          simp [implementation_cons] at h_result_zero
          have h_nonneg : 0 ≤ row.sum / capacity + (if row.sum % capacity > 0 then 1 else 0) := by
            apply Nat.zero_le
          have h_nonneg2 : 0 ≤ implementation rest capacity := by
            apply Nat.zero_le
          linarith
      · intro h_empty
        simp [h_empty, implementation_empty]
    · intro h_nonempty
      cases grid with
      | nil => contradiction
      | cons row rest =>
        simp [List.head!, List.tail!]
        rw [implementation_cons]
        simp
        ring