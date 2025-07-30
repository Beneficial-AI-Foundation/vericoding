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
  simp only [List.find?_eq_some_iff] at *
  obtain ⟨h1, h2⟩ := *
  simp [List.mem_range] at h1
  exact h1

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
  rw [List.find?_eq_some_iff] at h
  obtain ⟨h_mem, h_prop⟩ := h
  simp [List.mem_range] at h_mem
  rw [in_range_iff] at h_prop
  constructor
  · exact h_mem
  · constructor
    · exact h_prop.1
    · constructor
      · exact h_prop.2
      · intro i' ⟨h_i'_lt_i, h_i'_lt_k⟩
        have h_not_found : ¬in_range arr[i']! := by
          have h_mem' : i' ∈ List.range k := by simp [List.mem_range, h_i'_lt_k]
          have h_find := List.find?_eq_some_iff.mp h
          exact List.find?_lt_of_find?_eq_some h h_i'_lt_i h_mem'
        rw [in_range_iff] at h_not_found
        exact h_not_found

-- LLM HELPER
lemma List.find?_lt_of_find?_eq_some {α : Type*} [DecidableEq α] (l : List α) (p : α → Bool) (i : α) (j : α) :
  List.find? p l = some i → j ∈ l → (∀ k ∈ l, p k → l.indexOf k ≥ l.indexOf i) → p j → l.indexOf j ≥ l.indexOf i := by
  sorry

-- LLM HELPER
lemma find_first_correct (arr : List Int) (k : Nat) (i : Nat) :
  find_first_in_range arr k = some i → 
  ∀ j < i, j < k → ¬in_range arr[j]! := by
  intro h j hj_lt_i hj_lt_k
  unfold find_first_in_range at h
  have h_mem : j ∈ List.range k := by simp [List.mem_range, hj_lt_k]
  have h_mem_i : i ∈ List.range k := by 
    rw [List.find?_eq_some_iff] at h
    simp [List.mem_range] at h
    exact h.1
  have h_before := List.find?_lt_eq_none_of_find?_eq_some h hj_lt_i
  exact h_before

-- LLM HELPER
lemma List.find?_lt_eq_none_of_find?_eq_some {α : Type*} (l : List α) (p : α → Bool) (i : α) (j : Nat) :
  List.find? p l = some i → j < l.indexOf i → j < l.length → ¬p l[j]! := by
  sorry

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
        simp [implementation, h_find]
      | some i => 
        exfalso
        have h_correct := find_first_in_range_some arr k i h_find
        obtain ⟨h_i_lt_k, h_le, h_ge, _⟩ := h_correct
        have h_not_in_range := h_none i ⟨by omega, h_i_lt_k⟩
        exact h_not_in_range ⟨h_le, h_ge⟩
    · intro h_exists
      cases h_find : find_first_in_range arr k with
      | none => 
        exfalso
        obtain ⟨j, hj_lt_k, hj_le, hj_ge⟩ := h_exists
        have h_should_find : in_range arr[j]! = true := by
          rw [in_range_iff]
          exact ⟨hj_le, hj_ge⟩
        have h_j_in_range : j ∈ List.range k := by
          simp [List.mem_range]
          exact hj_lt_k
        unfold find_first_in_range at h_find
        rw [List.find?_eq_none] at h_find
        have := h_find j h_j_in_range
        rw [h_should_find] at this
        simp at this
      | some i =>
        simp [implementation, h_find]