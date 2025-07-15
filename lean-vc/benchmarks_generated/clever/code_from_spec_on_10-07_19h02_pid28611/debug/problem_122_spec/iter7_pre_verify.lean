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
  (∃ i, i < k
    ∧ arr[i]! ≤ 99 ∧ -99 ≤ arr[i]!
    ∧ result = arr[i]! + (if i = 0 then 0 else implementation arr i)
    ∧ ∀ i', i < i' ∧ i' < k → ¬(arr[i']! ≤ 99 ∧ -99 ≤ arr[i']!)) → result = 0
∃ result, implementation arr k = result ∧
spec result

-- LLM HELPER
def in_range (x : Int) : Bool := x ≤ 99 && -99 ≤ x

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
  obtain ⟨_, _, h_mem, _⟩ := *
  simp [List.mem_range] at h_mem
  exact h_mem

-- LLM HELPER
lemma in_range_iff (x : Int) : in_range x = true ↔ x ≤ 99 ∧ -99 ≤ x := by
  simp [in_range, Bool.and_eq_true]

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
  ∀ i', i' < i ∧ i' < k → ¬(arr[i']! ≤ 99 ∧ -99 ≤ arr[i']!) := by
  intro h
  unfold find_first_in_range at h
  rw [List.find?_eq_some_iff_append] at h
  obtain ⟨as, bs, h_eq, h_prop⟩ := h
  have h_mem : i ∈ List.range k := by
    rw [h_eq]
    simp [List.mem_append]
  simp [List.mem_range] at h_mem
  have h_in_range : in_range arr[i]! = true := by
    rw [h_eq] at h_prop
    simp at h_prop
    exact h_prop.2
  rw [in_range_iff] at h_in_range
  constructor
  · exact h_mem
  · constructor
    · exact h_in_range.1
    · constructor
      · exact h_in_range.2
      · intro i' ⟨h_i'_lt_i, h_i'_lt_k⟩
        have h_not_found : ¬in_range arr[i']! = true := by
          have h_mem' : i' ∈ as := by
            rw [h_eq] at h_prop
            simp at h_prop
            have h_i'_mem : i' ∈ List.range k := by simp [List.mem_range, h_i'_lt_k]
            rw [← h_eq] at h_i'_mem
            simp [List.mem_append] at h_i'_mem
            cases h_i'_mem with
            | inl h => exact h
            | inr h => 
              simp at h
              cases h with
              | inl h => subst h; exact False.elim (Nat.lt_irrefl i h_i'_lt_i)
              | inr h => exact False.elim (Nat.not_lt.mpr (Nat.le_of_lt h_i'_lt_i) h_i'_lt_i)
          exact h_prop.1 i' h_mem'
        rw [in_range_iff] at h_not_found
        exact h_not_found

theorem correctness
(arr: List Int)
(k: Nat)
: problem_spec implementation arr k := by
  unfold problem_spec
  use implementation arr k
  constructor
  · rfl
  · intro h_len_ge h_len_le h_k_ge h_k_le
    cases h_find : find_first_in_range arr k with
    | none => 
      simp [implementation, h_find]
      constructor
      · intro h_none
        exact find_first_in_range_none arr k h_find
      · intro h_exists
        exfalso
        obtain ⟨i, h_i_lt_k, h_i_in_range, _, _⟩ := h_exists
        have h_contra := find_first_in_range_none arr k h_find i ⟨Nat.zero_le i, h_i_lt_k⟩
        exact h_contra h_i_in_range
    | some i => 
      simp [implementation, h_find]
      constructor
      · intro h_none
        exfalso
        have h_some := find_first_in_range_some arr k i h_find
        obtain ⟨_, h_i_in_range, _, _⟩ := h_some
        have h_contra := h_none i ⟨Nat.zero_le i, h_some.1⟩
        exact h_contra h_i_in_range
      · intro h_exists
        rfl