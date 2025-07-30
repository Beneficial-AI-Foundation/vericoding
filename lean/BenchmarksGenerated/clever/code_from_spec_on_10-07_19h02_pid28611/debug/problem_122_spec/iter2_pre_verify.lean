import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
(implementation: List Int → Nat → Int)
(arr: List Int)
(k: Nat) :=
let spec (result: Int) :=
  1 ≤ arr.length → arr.length ≤ 100 → 1 ≤ k → k ≤ arr.length →
  ((∀ i, 0 ≤ i ∧ i < k → ¬(arr[i]! ≤ 99 ∧ -99 ≤ arr[i]!)) → result = 0) ∧
  ∃ i, i < k
    ∧ arr[i]! ≤ 99 ∧ -99 ≤ arr[i]!
    ∧ result = arr[i]! + (if i = 0 then 0 else implementation arr i)
    ∧ ∀ i', i < i' ∧ i' < k → ¬(arr[i']! ≤ 99 ∧ -99 ≤ arr[i']!)
∃ result, implementation arr k = result ∧
spec result

-- LLM HELPER
def in_range (x : Int) : Bool := x ≤ 99 ∧ -99 ≤ x

-- LLM HELPER
def find_first_in_range (arr : List Int) (k : Nat) : Option Nat :=
  (List.range k).find? (fun i => in_range arr[i]!)

def implementation (arr: List Int) (k: Nat) : Int :=
  match find_first_in_range arr k with
  | none => 0
  | some i => arr[i]! + (if i = 0 then 0 else implementation arr i)
termination_by k
decreasing_by
  unfold find_first_in_range at *
  simp only [List.find?_eq_some_iff_append] at *
  obtain ⟨left, right, h1, h2, h3⟩ := *
  simp [List.mem_range] at h3
  exact h3

-- LLM HELPER
lemma in_range_iff (x : Int) : in_range x = true ↔ x ≤ 99 ∧ -99 ≤ x := by
  simp [in_range]

-- LLM HELPER
lemma find_first_in_range_none (arr : List Int) (k : Nat) :
  find_first_in_range arr k = none → ∀ i, 0 ≤ i ∧ i < k → ¬(arr[i]! ≤ 99 ∧ -99 ≤ arr[i]!) := by
  intro h i ⟨hi_ge, hi_lt⟩
  unfold find_first_in_range at h
  rw [List.find?_eq_none] at h
  have h_mem : i ∈ List.range k := by simp [List.mem_range, hi_ge, hi_lt]
  have h_not_in_range := h i h_mem
  rw [in_range_iff] at h_not_in_range
  exact h_not_in_range

-- LLM HELPER
lemma find_first_in_range_some (arr : List Int) (k : Nat) (i : Nat) :
  find_first_in_range arr k = some i → i < k ∧ arr[i]! ≤ 99 ∧ -99 ≤ arr[i]! ∧ 
  ∀ i', i < i' ∧ i' < k → ¬(arr[i']! ≤ 99 ∧ -99 ≤ arr[i']!) := by
  intro h
  unfold find_first_in_range at h
  rw [List.find?_eq_some_iff_append] at h
  obtain ⟨left, right, h1, h2, h3⟩ := h
  simp [List.mem_range] at h3
  constructor
  · exact h3
  · constructor
    · rw [in_range_iff] at h2
      exact h2.1
    · constructor
      · rw [in_range_iff] at h2
        exact h2.2
      · intro i' ⟨h_i_lt_i', h_i'_lt_k⟩
        have h_in_left : i' ∈ left := by
          rw [h1] at h_i'_lt_k
          simp [List.mem_range] at h_i'_lt_k
          rw [h1]
          simp [List.mem_range, h_i_lt_i']
        have h_not_in_range := List.mem_filter.mp (by rw [← h1]; exact h_in_left)
        rw [in_range_iff] at h_not_in_range
        exact h_not_in_range.2

theorem correctness
(arr: List Int)
(k: Nat)
: problem_spec implementation arr k := by
  unfold problem_spec
  use implementation arr k
  constructor
  · rfl
  · intro h_len_ge h_len_le h_k_ge h_k_le
    constructor
    · intro h_none
      cases h_find : find_first_in_range arr k with
      | none => 
        simp [implementation]
        rw [h_find]
        simp
      | some i => 
        exfalso
        have h_correct := find_first_in_range_some arr k i h_find
        obtain ⟨h_i_lt_k, h_le, h_ge, _⟩ := h_correct
        have h_not_in_range := h_none i ⟨by omega, h_i_lt_k⟩
        exact h_not_in_range ⟨h_le, h_ge⟩
    · cases h_find : find_first_in_range arr k with
      | none => 
        exfalso
        have h_all_out := find_first_in_range_none arr k h_find
        -- This case contradicts the existence claim in the problem spec
        -- We need to show that there exists some i with the property
        sorry
      | some i =>
        use i
        have h_correct := find_first_in_range_some arr k i h_find
        obtain ⟨h_i_lt_k, h_le, h_ge, h_first⟩ := h_correct
        constructor
        · exact h_i_lt_k
        · constructor
          · exact ⟨h_le, h_ge⟩
          · constructor
            · simp [implementation]
              rw [h_find]
              simp
            · exact h_first