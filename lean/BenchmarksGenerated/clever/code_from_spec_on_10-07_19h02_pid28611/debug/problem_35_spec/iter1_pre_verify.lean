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
lemma list_maximum_ge (l : List Int) (h : Int) (x : Int) :
  x ∈ l → x ≤ List.foldl max h l := by
  induction l generalizing h with
  | nil => intro h_mem; exact False.elim h_mem
  | cons y ys ih =>
    intro h_mem
    simp [List.foldl]
    cases h_mem with
    | head => 
      simp [max_def]
      by_cases hcmp : h ≤ y
      · simp [hcmp]
        exact le_refl y
      · simp [hcmp]
        exact le_of_not_le hcmp
    | tail h_tail =>
      have := ih (max h y) h_tail
      exact this

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
lemma get_mem_of_lt_length (l : List Int) (i : Nat) (h : i < l.length) :
  l.get! i ∈ l := by
  exact List.getElem!_mem l i

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
        simp [List.length] at hi
        have h_mem := get_mem_of_lt_length (h :: t) i hi
        cases Nat.eq_zero_or_pos i with
        | inl h_zero =>
          simp [h_zero, List.get!]
          exact head_le_maximum t h
        | inr h_pos_i =>
          simp [List.get!] at h_mem
          have : List.get! (h :: t) i ∈ (h :: t) := h_mem
          exact list_maximum_ge t h (List.get! (h :: t) i) this
      · have h_cases := list_maximum_mem t h
        cases h_cases with
        | inl h_eq =>
          use 0
          simp [List.length, List.get!, h_eq]
        | inr h_mem =>
          have : ∃ i, i < (h :: t).length ∧ (h :: t).get! i = List.foldl max h t := by
            have h_pos := List.mem_iff_get.mp (List.mem_cons_of_mem h h_mem)
            obtain ⟨i, hi, h_eq⟩ := h_pos
            use i + 1
            constructor
            · simp [List.length]
              exact Nat.succ_lt_succ hi
            · simp [List.get!]
              exact h_eq
          exact this