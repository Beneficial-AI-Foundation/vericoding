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
  if grid.length = 0 then 0
  else
    let well_water_count := grid.head!.sum
    let buckets_needed := well_water_count / capacity + (if well_water_count % capacity > 0 then 1 else 0)
    buckets_needed + implementation grid.tail! capacity

-- LLM HELPER
lemma implementation_empty (capacity: Nat) : implementation [] capacity = 0 := by
  simp [implementation]

-- LLM HELPER
lemma implementation_nonempty (grid: List (List Nat)) (capacity: Nat) (h: grid.length > 0) :
  implementation grid capacity = 
    let well_water_count := grid.head!.sum
    let buckets_needed := well_water_count / capacity + (if well_water_count % capacity > 0 then 1 else 0)
    buckets_needed + implementation grid.tail! capacity := by
  simp [implementation]
  rw [if_neg]
  simp [Ne.symm (ne_of_gt h)]

-- LLM HELPER
lemma buckets_needed_pos (water: Nat) (capacity: Nat) (h: capacity > 0) :
  water / capacity + (if water % capacity > 0 then 1 else 0) > 0 ↔ water > 0 := by
  constructor
  · intro h_pos
    by_contra h_zero
    simp at h_zero
    rw [h_zero] at h_pos
    simp at h_pos
  · intro h_water_pos
    by_cases h_div : water / capacity > 0
    · simp [Nat.pos_iff_ne_zero.mp h_div]
    · simp at h_div
      have h_lt : water < capacity := Nat.div_eq_zero_iff_lt.mp h_div
      have h_mod : water % capacity = water := Nat.mod_eq_of_lt h_lt
      rw [h_mod]
      simp [h_water_pos]

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
        by_cases h_empty : grid.length = 0
        · exact h_empty
        · rw [implementation_nonempty grid capacity (Nat.pos_of_ne_zero h_empty)] at h_result_zero
          simp at h_result_zero
          exfalso
          have h_tail_nonneg : implementation grid.tail! capacity ≥ 0 := Nat.zero_le _
          have h_buckets_nonneg : grid.head!.sum / capacity + (if grid.head!.sum % capacity > 0 then 1 else 0) ≥ 0 := Nat.zero_le _
          rw [Nat.add_eq_zero_iff] at h_result_zero
          cases h_result_zero with
          | mk h_buckets_zero h_tail_zero =>
            have : grid.head!.sum = 0 := by
              by_cases h_mod : grid.head!.sum % capacity > 0
              · simp [h_mod] at h_buckets_zero
              · simp [h_mod] at h_buckets_zero
                rw [Nat.div_eq_zero_iff_lt] at h_buckets_zero
                have : grid.head!.sum % capacity = grid.head!.sum := Nat.mod_eq_of_lt h_buckets_zero
                rw [this] at h_mod
                simp at h_mod
                exact Nat.eq_zero_of_le_zero (le_of_not_gt h_mod)
            rw [this] at h_buckets_zero
            simp at h_buckets_zero
      · intro h_empty
        rw [implementation_empty]
    · intro h_nonempty
      rw [implementation_nonempty grid capacity h_nonempty]
      simp
      ring