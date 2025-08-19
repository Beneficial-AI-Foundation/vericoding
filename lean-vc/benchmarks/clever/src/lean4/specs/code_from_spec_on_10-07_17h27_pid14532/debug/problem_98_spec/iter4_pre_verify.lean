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
  let rec count_vowels (chars : List Char) : Int :=
    match chars with
    | [] => 0
    | c :: rest => 
      if is_uppercase_vowel c then 1 + count_vowels rest
      else count_vowels rest
  count_vowels chars

-- LLM HELPER
lemma is_uppercase_vowel_correct (c : Char) : 
  is_uppercase_vowel c = true ↔ c ∈ ['A', 'E', 'I', 'O', 'U'] := by
  simp [is_uppercase_vowel]
  constructor
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
lemma count_vowels_correct (chars : List Char) : 
  let rec count_vowels (chars : List Char) : Int :=
    match chars with
    | [] => 0
    | c :: rest => 
      if is_uppercase_vowel c then 1 + count_vowels rest
      else count_vowels rest
  count_vowels chars = (chars.filter (fun c => is_uppercase_vowel c)).length := by
  induction chars with
  | nil => simp
  | cons c rest ih =>
    simp
    if h : is_uppercase_vowel c then
      simp [h]
      rw [ih]
      simp
    else
      simp [h]
      rw [ih]

theorem correctness
(s: String)
: problem_spec implementation s
:= by
  simp [problem_spec, implementation]
  let chars := s.toList
  let uppercase_vowels := ['A', 'E', 'I', 'O', 'U']
  let rec count_vowels (chars : List Char) : Int :=
    match chars with
    | [] => 0
    | c :: rest => 
      if is_uppercase_vowel c then 1 + count_vowels rest
      else count_vowels rest
  
  use count_vowels chars
  constructor
  · rfl
  · constructor
    · constructor
      · intro h
        intro i hi
        by_contra h_contra
        have : count_vowels chars > 0 := by
          rw [count_vowels_correct]
          simp [List.length_pos_iff_exists_mem]
          use chars[i]!
          constructor
          · rw [List.mem_filter]
            constructor
            · exact List.getElem_mem chars i hi
            · rw [is_uppercase_vowel_correct]
              exact h_contra
          · rfl
        simp [h] at this
      · intro h
        by_contra h_contra
        push_neg at h_contra
        obtain ⟨i, hi, h_mem⟩ := h_contra
        have : count_vowels chars > 0 := by
          rw [count_vowels_correct]
          simp [List.length_pos_iff_exists_mem]
          use chars[i]!
          constructor
          · rw [List.mem_filter]
            constructor
            · exact List.getElem_mem chars i hi
            · rw [is_uppercase_vowel_correct]
              exact h_mem
          · rfl
        have : count_vowels chars = 0 := h
        simp [this] at *
    · intro h_len
      by_cases h_first : chars[0]! ∈ uppercase_vowels
      · left
        constructor
        · simp [count_vowels]
          split
          · simp
            rw [is_uppercase_vowel_correct] at *
            exact h_first
          · rw [is_uppercase_vowel_correct] at *
            contradiction
        · exact h_first
      · right
        constructor
        · simp [count_vowels]
          split
          · rw [is_uppercase_vowel_correct] at *
            contradiction
          · simp
        · exact h_first