import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(impl: Nat → Nat → List Nat)
-- inputs
(a b : Nat) :=
let isAscendingBy2 (r : List Nat) :=
∀ i, i < r.length - 1 → r[i+1]! - r[i]! = 2
-- spec
let spec (result: List Nat) :=
result.all (fun n => n % 2 = 0) ∧ isAscendingBy2 result ∧
1 < result.length ∧
let min_a_b := min a b;
let max_a_b := max a b;
if min_a_b = max_a_b ∧ (min_a_b % 2 = 1)
then result = []
else ((result[0]! = if 2 ∣ min_a_b then min_a_b else (min_a_b + 1)) ∧
(result[result.length-1]! = if 2 ∣ max_a_b then max_a_b else max_a_b - 1))
-- program terminates
∃ result, impl a b = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
def range_evens (start_even finish_even : Nat) : List Nat :=
  if start_even > finish_even then []
  else List.range ((finish_even - start_even) / 2 + 1) |>.map (fun i => start_even + 2 * i)

def implementation (a b: Nat) : List Nat := 
  let min_a_b := min a b
  let max_a_b := max a b
  if min_a_b = max_a_b ∧ (min_a_b % 2 = 1) then []
  else 
    let start_even := if 2 ∣ min_a_b then min_a_b else (min_a_b + 1)
    let end_even := if 2 ∣ max_a_b then max_a_b else max_a_b - 1
    range_evens start_even end_even

-- LLM HELPER
lemma range_evens_all_even (start_even finish_even : Nat) (h : start_even % 2 = 0) :
  (range_evens start_even finish_even).all (fun n => n % 2 = 0) := by
  simp [range_evens]
  by_cases h_comp : start_even > finish_even
  · simp [h_comp]
  · simp [h_comp]
    intro i hi
    simp [List.mem_map]
    intro j hj
    simp [Nat.add_mod, h]

-- LLM HELPER
lemma range_evens_ascending (start_even finish_even : Nat) (h : start_even % 2 = 0) :
  let r := range_evens start_even finish_even
  ∀ i, i < r.length - 1 → r[i+1]! - r[i]! = 2 := by
  intro i hi
  simp [range_evens]
  by_cases h_comp : start_even > finish_even
  · simp [h_comp] at hi
    omega
  · simp [h_comp] at hi ⊢
    simp [List.getElem_map, List.getElem_range]
    ring

-- LLM HELPER
lemma range_evens_nonempty (start_even finish_even : Nat) (h1 : start_even % 2 = 0) (h2 : finish_even % 2 = 0) (h3 : start_even ≤ finish_even) :
  1 < (range_evens start_even finish_even).length := by
  simp [range_evens, h3]
  have : finish_even ≥ start_even := h3
  have : (finish_even - start_even) / 2 + 1 ≥ 1 := by
    simp [Nat.div_add_mod']
    omega
  omega

-- LLM HELPER
lemma range_evens_first_last (start_even finish_even : Nat) (h1 : start_even % 2 = 0) (h2 : finish_even % 2 = 0) (h3 : start_even ≤ finish_even) :
  let r := range_evens start_even finish_even
  r[0]! = start_even ∧ r[r.length - 1]! = finish_even := by
  simp [range_evens, h3]
  constructor
  · simp [List.getElem_map, List.getElem_range]
  · simp [List.getElem_map, List.getElem_range]
    have len_pos : 0 < (finish_even - start_even) / 2 + 1 := by omega
    simp [Nat.sub_sub, len_pos]
    ring

theorem correctness
(a b: Nat)
: problem_spec implementation a b := by
  simp [problem_spec]
  let min_a_b := min a b
  let max_a_b := max a b
  use implementation a b
  constructor
  · rfl
  · simp [implementation]
    by_cases h_case : min_a_b = max_a_b ∧ (min_a_b % 2 = 1)
    · simp [h_case]
    · simp [h_case]
      let start_even := if 2 ∣ min_a_b then min_a_b else (min_a_b + 1)
      let end_even := if 2 ∣ max_a_b then max_a_b else max_a_b - 1
      have h_start_even : start_even % 2 = 0 := by
        simp [start_even]
        by_cases h : 2 ∣ min_a_b
        · simp [h, Nat.dvd_iff_mod_eq_zero.mp h]
        · simp [h]
          rw [Nat.add_mod]
          have : min_a_b % 2 = 1 := by
            have : min_a_b % 2 ≠ 0 := Nat.dvd_iff_mod_eq_zero.not.mp h
            omega
          simp [this]
      have h_end_even : end_even % 2 = 0 := by
        simp [end_even]
        by_cases h : 2 ∣ max_a_b
        · simp [h, Nat.dvd_iff_mod_eq_zero.mp h]
        · simp [h]
          rw [Nat.sub_mod]
          have : max_a_b % 2 = 1 := by
            have : max_a_b % 2 ≠ 0 := Nat.dvd_iff_mod_eq_zero.not.mp h
            omega
          simp [this]
      have h_order : start_even ≤ end_even := by
        simp [start_even, end_even]
        by_cases h1 : 2 ∣ min_a_b <;> by_cases h2 : 2 ∣ max_a_b
        · simp [h1, h2]
          exact min_le_max a b
        · simp [h1, h2]
          have : min_a_b ≤ max_a_b - 1 := by
            have : min_a_b < max_a_b := by
              push_neg at h_case
              cases' h_case with h_neq h_odd
              by_contra h_not_lt
              have : max_a_b ≤ min_a_b := le_of_not_gt h_not_lt
              have : min_a_b = max_a_b := le_antisymm (min_le_max a b) this
              exact h_neq this
            omega
          exact this
        · simp [h1, h2]
          have : min_a_b + 1 ≤ max_a_b := by
            have : min_a_b < max_a_b := by
              push_neg at h_case
              cases' h_case with h_neq h_odd
              by_contra h_not_lt
              have : max_a_b ≤ min_a_b := le_of_not_gt h_not_lt
              have : min_a_b = max_a_b := le_antisymm (min_le_max a b) this
              exact h_neq this
            omega
          exact this
        · simp [h1, h2]
          have : min_a_b + 1 ≤ max_a_b - 1 := by
            have : min_a_b < max_a_b := by
              push_neg at h_case
              cases' h_case with h_neq h_odd
              by_contra h_not_lt
              have : max_a_b ≤ min_a_b := le_of_not_gt h_not_lt
              have : min_a_b = max_a_b := le_antisymm (min_le_max a b) this
              exact h_neq this
            omega
          exact this
      constructor
      · exact range_evens_all_even start_even end_even h_start_even
      constructor
      · exact range_evens_ascending start_even end_even h_start_even
      constructor
      · exact range_evens_nonempty start_even end_even h_start_even h_end_even h_order
      · exact range_evens_first_last start_even end_even h_start_even h_end_even h_order