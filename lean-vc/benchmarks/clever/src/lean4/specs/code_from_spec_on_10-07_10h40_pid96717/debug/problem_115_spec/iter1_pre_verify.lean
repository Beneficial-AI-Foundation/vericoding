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
  simp [Nat.not_eq_zero_of_zero_lt h]

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
          have : implementation grid.tail! capacity ≥ 0 := Nat.zero_le _
          have : grid.head!.sum / capacity + (if grid.head!.sum % capacity > 0 then 1 else 0) ≥ 1 := by
            by_cases h_mod : grid.head!.sum % capacity > 0
            · simp [h_mod]
              omega
            · simp [h_mod]
              have : grid.head!.sum / capacity ≥ 1 := by
                by_contra h_contra
                simp at h_contra
                have : grid.head!.sum < capacity := by
                  rw [Nat.div_eq_zero_iff_lt] at h_contra
                  exact h_contra
                have : grid.head!.sum % capacity = grid.head!.sum := Nat.mod_eq_of_lt this
                rw [this] at h_mod
                simp at h_mod
                have : grid.head!.sum = 0 := Nat.eq_zero_of_le_zero (le_of_not_gt h_mod)
                rw [this] at h_contra
                simp at h_contra
              omega
          omega
      · intro h_empty
        rw [implementation_empty]
    · intro h_nonempty
      rw [implementation_nonempty grid capacity h_nonempty]
      simp
      omega