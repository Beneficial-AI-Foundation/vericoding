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
  if chars.isEmpty then 0
  else if chars.length = 1 then
    if is_uppercase_vowel chars[0]! then 1 else 0
  else
    let rest := implementation (chars.drop 1).toString
    if is_uppercase_vowel chars[0]! then rest + 1 else rest

-- LLM HELPER
lemma is_uppercase_vowel_correct (c : Char) :
  is_uppercase_vowel c = true ↔ c ∈ ['A', 'E', 'I', 'O', 'U'] := by
  simp [is_uppercase_vowel]
  constructor
  · intro h
    simp at h
    cases' h with h h
    · simp [h]
    · cases' h with h h
      · simp [h]
      · cases' h with h h
        · simp [h]
        · cases' h with h h
          · simp [h]
          · simp [h]
  · intro h
    simp at h
    cases' h with h h
    · simp [h]
    · cases' h with h h
      · simp [h]
      · cases' h with h h
        · simp [h]
        · cases' h with h h
          · simp [h]
          · simp [h]

-- LLM HELPER
lemma implementation_counts_vowels (s : String) :
  implementation s = (s.toList.filter (fun c => is_uppercase_vowel c)).length := by
  induction s using String.toList.induction_on with
  | nil => simp [implementation, is_uppercase_vowel]
  | cons c s ih =>
    simp [implementation]
    by_cases h : is_uppercase_vowel c
    · simp [h]
      rw [ih]
      simp [List.filter_cons, h]
    · simp [h]
      rw [ih]
      simp [List.filter_cons, h]

theorem correctness
(s: String)
: problem_spec implementation s := by
  unfold problem_spec
  use implementation s
  constructor
  · rfl
  · constructor
    · constructor
      · intro h
        intro i hi
        rw [implementation_counts_vowels] at h
        simp at h
        by_contra hc
        have : (s.toList.filter (fun c => is_uppercase_vowel c)).length > 0 := by
          apply List.length_pos_of_mem
          apply List.mem_filter_of_mem
          · exact List.get_mem _ _ _
          · rwa [is_uppercase_vowel_correct]
        rw [h] at this
        simp at this
      · intro h
        rw [implementation_counts_vowels]
        simp
        intro c hc
        rw [←is_uppercase_vowel_correct]
        by_contra hcontra
        have : c ∉ ['A', 'E', 'I', 'O', 'U'] := by
          rwa [is_uppercase_vowel_correct] at hcontra
        obtain ⟨i, hi, hget⟩ := List.mem_iff_get.mp hc
        rw [←hget] at this
        exact h i hi this
    · intro _
      left
      constructor
      · intro h
        sorry
      · intro h
        sorry