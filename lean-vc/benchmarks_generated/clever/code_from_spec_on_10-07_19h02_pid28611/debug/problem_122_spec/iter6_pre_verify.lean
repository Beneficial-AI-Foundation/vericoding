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
  simp only [List.find?_eq_some] at *
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
  rw [List.find?_eq_some] at h
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
          have h_find := List.find?_eq_some.mp h
          have h_before := List.find?_before_first_match (List.range k) (fun j => in_range arr[j]!) i' i h_mem' h_mem h_prop h_i'_lt_i
          exact h_before
        rw [in_range_iff] at h_not_found
        exact h_not_found

-- LLM HELPER
lemma List.find?_before_first_match {α : Type*} (l : List α) (p : α → Bool) (x y : α) :
  x ∈ l → y ∈ l → p y → l.indexOf x < l.indexOf y → ¬p x := by
  intro h_x_mem h_y_mem h_p_y h_lt
  by_contra h_p_x
  have h_find_x : List.find? p l = some x := by
    rw [List.find?_eq_some]
    exact ⟨h_x_mem, h_p_x⟩
  have h_find_y : List.find? p l = some y := by
    rw [List.find?_eq_some]
    exact ⟨h_y_mem, h_p_y⟩
  have h_first : List.find? p l = some (l.filter p).head! := by
    rw [List.find?_eq_some]
    simp [List.filter_eq_nil_iff]
    cases' h_ex : l.filter p with
    | nil => simp at h_ex; rw [← h_ex] at h_p_x; simp at h_p_x
    | cons hd tl => simp [List.head!]
  rw [h_find_x] at h_find_y
  injection h_find_y
  subst this
  simp at h_lt

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
      intro h_none
      simp
    | some i => 
      simp [implementation, h_find]
      intro h_exists
      simp