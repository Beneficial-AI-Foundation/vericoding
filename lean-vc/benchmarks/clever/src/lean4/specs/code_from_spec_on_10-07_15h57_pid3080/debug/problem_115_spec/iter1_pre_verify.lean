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
lemma list_sum_nonneg (l : List Nat) : 0 ≤ l.sum := by
  simp [List.sum_nonneg]

-- LLM HELPER
lemma div_add_mod_helper (a b : Nat) (hb : b > 0) : 
  a / b + (if a % b > 0 then 1 else 0) = (a + b - 1) / b := by
  sorry

-- LLM HELPER
lemma implementation_zero_iff_empty (grid : List (List Nat)) (capacity : Nat) :
  implementation grid capacity = 0 ↔ grid.length = 0 := by
  cases grid with
  | nil => simp [implementation]
  | cons head tail => 
    simp [implementation]
    constructor
    · intro h
      simp at h
      sorry
    · intro h
      simp at h

-- LLM HELPER
lemma implementation_recursive_property (grid : List (List Nat)) (capacity : Nat) 
  (h : grid.length > 0) :
  let well_water_count := grid.head!.sum
  implementation grid capacity - (well_water_count / capacity) - (if well_water_count % capacity > 0 then 1 else 0) = 
  implementation grid.tail! capacity := by
  cases grid with
  | nil => simp at h
  | cons head tail =>
    simp [implementation, List.head!, List.tail!]
    ring

theorem correctness
(grid: List (List Nat))
(capacity: Nat)
: problem_spec implementation grid capacity := by
  use implementation grid capacity
  constructor
  · rfl
  · intro h_binary h_uniform
    constructor
    · exact implementation_zero_iff_empty grid capacity
    · intro h_nonempty
      exact implementation_recursive_property grid capacity h_nonempty