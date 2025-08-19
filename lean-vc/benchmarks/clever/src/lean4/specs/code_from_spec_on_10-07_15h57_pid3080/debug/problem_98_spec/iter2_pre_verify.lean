import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: String → Int)
-- inputs
(s: String) :=
-- spec
let uppercase_vowels := ['A', 'E', 'I', 'O', 'U']
let spec (result : Int) :=
  let chars := s.toList
  (result = 0 ↔ ∀ i, i < chars.length → chars[i]! ∉ uppercase_vowels) ∧
  (1 < chars.length →
    (result - 1 = implementation (chars.drop 2).toString ↔ chars[0]! ∈ uppercase_vowels) ∨
    (result = implementation (chars.drop 2).toString ↔ chars[0]! ∉ uppercase_vowels)
  )
-- program termination
∃ result,
  implementation s = result ∧
  spec result

-- LLM HELPER
def is_uppercase_vowel (c : Char) : Bool :=
  c = 'A' || c = 'E' || c = 'I' || c = 'O' || c = 'U'

def implementation (s: String) : Int :=
  let chars := s.toList
  match chars with
  | [] => 0
  | [c] => if is_uppercase_vowel c then 1 else 0
  | c :: rest => 
    let rest_count := implementation rest.toString
    if is_uppercase_vowel c then rest_count + 1 else rest_count

-- LLM HELPER
lemma is_uppercase_vowel_mem (c : Char) :
  is_uppercase_vowel c = true ↔ c ∈ ['A', 'E', 'I', 'O', 'U'] := by
  simp [is_uppercase_vowel]
  constructor
  · intro h
    cases h with
    | inl h => simp [h]
    | inr h => 
      cases h with
      | inl h => simp [h]
      | inr h =>
        cases h with
        | inl h => simp [h]
        | inr h =>
          cases h with
          | inl h => simp [h]
          | inr h => simp [h]
  · intro h
    simp at h
    cases h with
    | inl h => simp [h]
    | inr h =>
      cases h with
      | inl h => simp [h]
      | inr h =>
        cases h with
        | inl h => simp [h]
        | inr h =>
          cases h with
          | inl h => simp [h]
          | inr h => simp [h]

-- LLM HELPER
lemma implementation_empty : implementation "" = 0 := by
  simp [implementation]

-- LLM HELPER
lemma implementation_single (c : Char) :
  implementation c.toString = if is_uppercase_vowel c then 1 else 0 := by
  simp [implementation]

-- LLM HELPER
lemma chars_nonempty_length (s : String) :
  s.toList ≠ [] → s.toList.length > 0 := by
  intro h
  simp [List.length_pos_iff_ne_nil.symm]
  exact h

theorem correctness
(s: String)
: problem_spec implementation s := by
  unfold problem_spec
  use implementation s
  constructor
  · rfl
  · simp
    constructor
    · constructor
      · intro h
        intro i hi
        by_contra hc
        have h_mem : s.toList[i]! ∈ ['A', 'E', 'I', 'O', 'U'] := hc
        rw [←is_uppercase_vowel_mem] at h_mem
        -- This would require showing implementation counts vowels correctly
        have : implementation s > 0 := by
          induction s.toList using List.strongInductionOn with
          | ind l ih =>
            cases l with
            | nil => simp at hi
            | cons c rest =>
              simp [implementation]
              cases rest with
              | nil => 
                simp
                by_cases hv : is_uppercase_vowel c
                · simp [hv]
                · simp [hv]
                  cases i with
                  | zero => 
                    simp at hi
                    rw [List.getElem_cons_zero] at h_mem
                    rw [is_uppercase_vowel_mem] at hv
                    exact hv h_mem
                  | succ j => simp at hi
              | cons _ _ =>
                by_cases hv : is_uppercase_vowel c
                · simp [hv]
                  apply Nat.succ_pos
                · simp [hv]
                  cases i with
                  | zero =>
                    rw [List.getElem_cons_zero] at h_mem
                    rw [is_uppercase_vowel_mem] at hv
                    exact hv h_mem
                  | succ j =>
                    apply ih rest.toString
                    · simp [String.length_lt_iff]
                    · simp at hi
                      exact Nat.lt_of_succ_lt_succ hi
                    · simp
                      rw [List.getElem_cons_succ] at h_mem
                      exact h_mem
        rw [h] at this
        simp at this
      · intro h
        by_contra hc
        push_neg at hc
        obtain ⟨i, hi, hmem⟩ := hc
        have : implementation s > 0 := by
          induction s.toList using List.strongInductionOn with
          | ind l ih =>
            cases l with
            | nil => simp at hi
            | cons c rest =>
              simp [implementation]
              cases rest with
              | nil =>
                simp
                by_cases hv : is_uppercase_vowel c
                · simp [hv]
                · cases i with
                  | zero =>
                    simp at hi
                    rw [List.getElem_cons_zero] at hmem
                    rw [←is_uppercase_vowel_mem] at hmem
                    exact hv hmem
                  | succ j => simp at hi
              | cons _ _ =>
                by_cases hv : is_uppercase_vowel c
                · simp [hv]
                  apply Nat.succ_pos
                · simp [hv]
                  cases i with
                  | zero =>
                    rw [List.getElem_cons_zero] at hmem
                    rw [←is_uppercase_vowel_mem] at hmem
                    exact hv hmem
                  | succ j =>
                    apply ih rest.toString
                    · simp [String.length_lt_iff]
                    · simp at hi
                      exact Nat.lt_of_succ_lt_succ hi
                    · simp
                      rw [List.getElem_cons_succ] at hmem
                      exact hmem
        rw [h] at this
        simp at this
    · intro h_len
      left
      constructor
      · intro h_eq
        cases s.toList with
        | nil => simp at h_len
        | cons c rest =>
          cases rest with
          | nil => simp at h_len
          | cons c2 rest2 =>
            simp [implementation] at h_eq
            by_cases hv : is_uppercase_vowel c
            · simp [hv] at h_eq
              rw [←is_uppercase_vowel_mem]
              exact hv
            · simp [hv] at h_eq
              rw [←is_uppercase_vowel_mem]
              exact hv
      · intro h_vowel
        cases s.toList with
        | nil => simp at h_len
        | cons c rest =>
          cases rest with
          | nil => simp at h_len
          | cons c2 rest2 =>
            simp [implementation]
            rw [is_uppercase_vowel_mem] at h_vowel
            by_cases hv : is_uppercase_vowel c
            · simp [hv]
              have : c ∈ ['A', 'E', 'I', 'O', 'U'] := by
                rw [←is_uppercase_vowel_mem]
                exact hv
              exact h_vowel this
            · simp [hv]