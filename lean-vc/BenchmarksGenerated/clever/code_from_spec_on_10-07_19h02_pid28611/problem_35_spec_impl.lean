import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: List Int → Int)
-- inputs
(l: List Int) :=
-- spec
let spec (result: Int) :=
  l.length > 0 →
  ((∀ i, i < l.length → l.get! i ≤ result) ∧
  (∃ i, i < l.length ∧ l.get! i = result));
-- program termination
∃ result, implementation l = result ∧
spec result

def implementation (l: List Int) : Int := 
  match l with
  | [] => 0
  | h :: t => List.foldl max h t

-- LLM HELPER
lemma list_maximum_mem (l : List Int) (h : Int) : 
  List.foldl max h l = h ∨ List.foldl max h l ∈ l := by
  induction l generalizing h with
  | nil => left; rfl
  | cons x xs ih =>
    simp [List.foldl]
    have := ih (max h x)
    cases this with
    | inl h_eq => 
      by_cases hcmp : h ≤ x
      · simp [max_def, hcmp] at h_eq
        right
        exact List.mem_cons_of_mem x h_eq
      · simp [max_def, hcmp] at h_eq
        left
        exact h_eq
    | inr h_mem =>
      right
      exact List.mem_cons_of_mem x h_mem

-- LLM HELPER
lemma head_le_maximum (l : List Int) (h : Int) :
  h ≤ List.foldl max h l := by
  induction l generalizing h with
  | nil => exact le_refl h
  | cons x xs ih =>
    simp [List.foldl]
    have := ih (max h x)
    exact le_trans (le_max_left h x) this

-- LLM HELPER
lemma list_maximum_ge (l : List Int) (h : Int) (x : Int) :
  x ∈ l → x ≤ List.foldl max h l := by
  induction l generalizing h with
  | nil => intro h_mem; exact absurd h_mem (List.not_mem_nil x)
  | cons y ys ih =>
    intro h_mem
    simp [List.foldl]
    cases h_mem with
    | head => 
      exact le_trans (le_max_right h y) (head_le_maximum ys (max h y))
    | tail h_tail =>
      have := ih (max h y) h_tail
      exact this

-- LLM HELPER
lemma get_mem_of_lt_length (l : List Int) (i : Nat) (h : i < l.length) :
  l.get! i ∈ l := by
  rw [List.mem_iff_get]
  use ⟨i, h⟩
  rw [List.get!_pos]
  exact h

-- LLM HELPER
lemma foldl_max_ge_head (h : Int) (t : List Int) :
  h ≤ List.foldl max h t := by
  exact head_le_maximum t h

-- LLM HELPER
lemma foldl_max_ge_all (h : Int) (t : List Int) (x : Int) :
  x ∈ (h :: t) → x ≤ List.foldl max h t := by
  intro h_mem
  cases h_mem with
  | head => exact foldl_max_ge_head h t
  | tail h_tail => exact list_maximum_ge t h x h_tail

-- LLM HELPER
lemma mem_to_index (l : List Int) (x : Int) (h : x ∈ l) :
  ∃ i, i < l.length ∧ l.get! i = x := by
  rw [List.mem_iff_get] at h
  obtain ⟨i, h_eq⟩ := h
  use i.val
  constructor
  · exact i.isLt
  · rw [List.get!_pos]
    exact h_eq
    exact i.isLt

theorem correctness
(l: List Int)
: problem_spec implementation l
:= by
  unfold problem_spec
  simp [implementation]
  cases l with
  | nil =>
    use 0
    simp
  | cons h t =>
    use List.foldl max h t
    constructor
    · rfl
    · intro h_pos
      constructor
      · intro i hi
        have h_mem := get_mem_of_lt_length (h :: t) i hi
        exact foldl_max_ge_all h t (List.get! (h :: t) i) h_mem
      · have h_cases := list_maximum_mem t h
        cases h_cases with
        | inl h_eq =>
          use 0
          constructor
          · simp [List.length]
          · simp [List.get!, h_eq]
        | inr h_mem =>
          have h_idx := mem_to_index (h :: t) (List.foldl max h t) (List.mem_cons_of_mem h h_mem)
          obtain ⟨j, hj, h_eq⟩ := h_idx
          use j
          constructor
          · exact hj
          · exact h_eq