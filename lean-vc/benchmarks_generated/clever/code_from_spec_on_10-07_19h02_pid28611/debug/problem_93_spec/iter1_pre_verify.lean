import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: String → String)
-- inputs
(s: String) :=
-- spec
let spec (result : String) :=
  s.data.all (λ c => c.isAlpha) →
  result.length = s.length ∧
  (∀ i, i < s.length →
    let c := s.data.get! i;
    let c' := result.data.get! i;
    match c with
    | 'a' | 'e' | 'i' | 'o' | 'u' | 'A' | 'E' | 'I' | 'O' | 'U' =>
      c.isUpper → c'.val = c.toLower.val + 2 ∧
      c.isLower → c'.val = c.toUpper.val + 2
    | _ =>
      c.isUpper → c' = c.toLower ∧
      c.isLower → c' = c.toUpper)
-- program termination
∃ result,
  implementation s = result ∧
  spec result

-- LLM HELPER
def isVowel (c : Char) : Bool :=
  match c with
  | 'a' | 'e' | 'i' | 'o' | 'u' | 'A' | 'E' | 'I' | 'O' | 'U' => true
  | _ => false

-- LLM HELPER
def transformChar (c : Char) : Char :=
  if isVowel c then
    if c.isUpper then
      Char.ofNat (c.toLower.val + 2)
    else
      Char.ofNat (c.toUpper.val + 2)
  else
    if c.isUpper then
      c.toLower
    else
      c.toUpper

def implementation (s: String) : String := 
  ⟨s.data.map transformChar⟩

-- LLM HELPER
lemma map_length {α β : Type*} (f : α → β) (l : List α) : (l.map f).length = l.length := by
  induction l with
  | nil => simp
  | cons h t ih => simp [ih]

-- LLM HELPER
lemma get_map {α β : Type*} (f : α → β) (l : List α) (i : Nat) (h : i < l.length) : 
  (l.map f).get! i = f (l.get! i) := by
  have h' : i < (l.map f).length := by rw [map_length]; exact h
  rw [List.get!_eq_getD, List.get!_eq_getD, List.getD_map]

-- LLM HELPER
lemma isVowel_match (c : Char) : isVowel c = true ↔ 
  (c = 'a' ∨ c = 'e' ∨ c = 'i' ∨ c = 'o' ∨ c = 'u' ∨ c = 'A' ∨ c = 'E' ∨ c = 'I' ∨ c = 'O' ∨ c = 'U') := by
  constructor
  · intro h
    unfold isVowel at h
    cases c with
    | mk val =>
      simp at h
      cases h_eq : val with
      | _ => 
        simp [h_eq] at h
        cases h
  · intro h
    unfold isVowel
    cases h with
    | inl h => simp [h]
    | inr h => cases h with
      | inl h => simp [h]
      | inr h => cases h with
        | inl h => simp [h]
        | inr h => cases h with
          | inl h => simp [h]
          | inr h => cases h with
            | inl h => simp [h]
            | inr h => cases h with
              | inl h => simp [h]
              | inr h => cases h with
                | inl h => simp [h]
                | inr h => cases h with
                  | inl h => simp [h]
                  | inr h => cases h with
                    | inl h => simp [h]
                    | inr h => simp [h]

theorem correctness
(s: String)
: problem_spec implementation s
:= by
  unfold problem_spec
  use implementation s
  constructor
  · rfl
  · intro h_all_alpha
    constructor
    · unfold implementation
      simp [String.length]
      rw [map_length]
    · intro i h_i_lt
      unfold implementation
      simp [String.data]
      have h_map : (s.data.map transformChar).get! i = transformChar (s.data.get! i) := by
        apply get_map
        exact h_i_lt
      rw [h_map]
      let c := s.data.get! i
      unfold transformChar
      by_cases h_vowel : isVowel c
      · simp [h_vowel]
        rw [isVowel_match] at h_vowel
        cases h_vowel with
        | inl h => simp [h]; split_ifs <;> simp
        | inr h => cases h with
          | inl h => simp [h]; split_ifs <;> simp  
          | inr h => cases h with
            | inl h => simp [h]; split_ifs <;> simp
            | inr h => cases h with
              | inl h => simp [h]; split_ifs <;> simp
              | inr h => cases h with
                | inl h => simp [h]; split_ifs <;> simp
                | inr h => cases h with
                  | inl h => simp [h]; split_ifs <;> simp
                  | inr h => cases h with
                    | inl h => simp [h]; split_ifs <;> simp
                    | inr h => cases h with
                      | inl h => simp [h]; split_ifs <;> simp
                      | inr h => cases h with
                        | inl h => simp [h]; split_ifs <;> simp
                        | inr h => simp [h]; split_ifs <;> simp
      · simp [h_vowel]
        split_ifs with h_upper
        · simp [h_upper]
        · simp [h_upper]