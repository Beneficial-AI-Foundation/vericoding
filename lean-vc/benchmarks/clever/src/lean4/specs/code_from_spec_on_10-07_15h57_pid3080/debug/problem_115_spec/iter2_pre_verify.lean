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
lemma implementation_zero_iff_empty (grid : List (List Nat)) (capacity : Nat) :
  implementation grid capacity = 0 ↔ grid.length = 0 := by
  cases grid with
  | nil => simp [implementation]
  | cons head tail => 
    simp [implementation]
    constructor
    · intro h
      simp [List.sum] at h
      have : head.sum / capacity + (if head.sum % capacity > 0 then 1 else 0) + implementation tail capacity = 0 := h
      have h1 : head.sum / capacity + (if head.sum % capacity > 0 then 1 else 0) ≥ 1 := by
        cases' Classical.em (head.sum = 0) with h_zero h_nonzero
        · simp [h_zero]
          norm_num
        · have : head.sum > 0 := Nat.pos_of_ne_zero h_nonzero
          cases' Classical.em (head.sum % capacity = 0) with h_mod_zero h_mod_nonzero
          · simp [h_mod_zero]
            exact Nat.div_pos this (Nat.pos_of_ne_zero (by
              by_contra h_cap_zero
              simp [h_cap_zero] at h_mod_zero))
          · simp [h_mod_nonzero]
            exact Nat.succ_le_iff.mpr (Nat.add_pos_left (Nat.div_pos this (Nat.pos_of_ne_zero (by
              by_contra h_cap_zero
              simp [h_cap_zero] at h_mod_nonzero))))
      have h2 : implementation tail capacity ≥ 0 := Nat.zero_le _
      linarith
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
    rw [Nat.add_sub_cancel]

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