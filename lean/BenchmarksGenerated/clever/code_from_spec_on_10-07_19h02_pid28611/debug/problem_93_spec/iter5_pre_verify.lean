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
      Char.ofNat (c.toLower.val.toNat + 2)
    else
      Char.ofNat (c.toUpper.val.toNat + 2)
  else
    if c.isUpper then
      c.toLower
    else
      c.toUpper

def implementation (s: String) : String := 
  ⟨s.data.map transformChar⟩

-- LLM HELPER
lemma map_length (f : Char → Char) (l : List Char) : (l.map f).length = l.length := by
  induction l with
  | nil => simp
  | cons h t ih => simp [ih]

-- LLM HELPER
lemma get_map (f : Char → Char) (l : List Char) (i : Nat) (h : i < l.length) : 
  (l.map f).get! i = f (l.get! i) := by
  simp [List.get!_eq_getElem!, List.getElem_map]

-- LLM HELPER
lemma char_ofNat_val (n : Nat) : (Char.ofNat n).val = n := by
  simp [Char.ofNat]

-- LLM HELPER
lemma vowel_upper_transform (c : Char) (h_vowel : isVowel c = true) (h_upper : c.isUpper = true) :
  (transformChar c).val = c.toLower.val + 2 := by
  unfold transformChar
  simp [h_vowel, h_upper]
  rw [char_ofNat_val]
  simp [Nat.toNat]

-- LLM HELPER
lemma vowel_lower_transform (c : Char) (h_vowel : isVowel c = true) (h_lower : c.isLower = true) :
  (transformChar c).val = c.toUpper.val + 2 := by
  unfold transformChar
  simp [h_vowel, h_lower]
  rw [char_ofNat_val]
  simp [Nat.toNat]

-- LLM HELPER
lemma non_vowel_upper_transform (c : Char) (h_vowel : isVowel c = false) (h_upper : c.isUpper = true) :
  transformChar c = c.toLower := by
  unfold transformChar
  simp [h_vowel, h_upper]

-- LLM HELPER
lemma non_vowel_lower_transform (c : Char) (h_vowel : isVowel c = false) (h_lower : c.isLower = true) :
  transformChar c = c.toUpper := by
  unfold transformChar
  simp [h_vowel, h_lower]

-- LLM HELPER
lemma isVowel_spec (c : Char) : isVowel c = true ↔ 
  (c = 'a' ∨ c = 'e' ∨ c = 'i' ∨ c = 'o' ∨ c = 'u' ∨ c = 'A' ∨ c = 'E' ∨ c = 'I' ∨ c = 'O' ∨ c = 'U') := by
  constructor
  · intro h
    unfold isVowel at h
    split at h <;> simp at h
    · left; rfl
    · right; left; rfl
    · right; right; left; rfl
    · right; right; right; left; rfl
    · right; right; right; right; left; rfl
    · right; right; right; right; right; left; rfl
    · right; right; right; right; right; right; left; rfl
    · right; right; right; right; right; right; right; left; rfl
    · right; right; right; right; right; right; right; right; left; rfl
    · right; right; right; right; right; right; right; right; right; rfl
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
      by_cases h_vowel : isVowel c
      · rw [isVowel_spec] at h_vowel
        cases h_vowel with
        | inl h => 
          simp [h]; constructor
          · intro h_upper
            exact vowel_upper_transform c (by simp [isVowel, h]) h_upper
          · intro h_lower
            exact vowel_lower_transform c (by simp [isVowel, h]) h_lower
        | inr h => cases h with
          | inl h => 
            simp [h]; constructor
            · intro h_upper
              exact vowel_upper_transform c (by simp [isVowel, h]) h_upper
            · intro h_lower
              exact vowel_lower_transform c (by simp [isVowel, h]) h_lower
          | inr h => cases h with
            | inl h => 
              simp [h]; constructor
              · intro h_upper
                exact vowel_upper_transform c (by simp [isVowel, h]) h_upper
              · intro h_lower
                exact vowel_lower_transform c (by simp [isVowel, h]) h_lower
            | inr h => cases h with
              | inl h => 
                simp [h]; constructor
                · intro h_upper
                  exact vowel_upper_transform c (by simp [isVowel, h]) h_upper
                · intro h_lower
                  exact vowel_lower_transform c (by simp [isVowel, h]) h_lower
              | inr h => cases h with
                | inl h => 
                  simp [h]; constructor
                  · intro h_upper
                    exact vowel_upper_transform c (by simp [isVowel, h]) h_upper
                  · intro h_lower
                    exact vowel_lower_transform c (by simp [isVowel, h]) h_lower
                | inr h => cases h with
                  | inl h => 
                    simp [h]; constructor
                    · intro h_upper
                      exact vowel_upper_transform c (by simp [isVowel, h]) h_upper
                    · intro h_lower
                      exact vowel_lower_transform c (by simp [isVowel, h]) h_lower
                  | inr h => cases h with
                    | inl h => 
                      simp [h]; constructor
                      · intro h_upper
                        exact vowel_upper_transform c (by simp [isVowel, h]) h_upper
                      · intro h_lower
                        exact vowel_lower_transform c (by simp [isVowel, h]) h_lower
                    | inr h => cases h with
                      | inl h => 
                        simp [h]; constructor
                        · intro h_upper
                          exact vowel_upper_transform c (by simp [isVowel, h]) h_upper
                        · intro h_lower
                          exact vowel_lower_transform c (by simp [isVowel, h]) h_lower
                      | inr h => cases h with
                        | inl h => 
                          simp [h]; constructor
                          · intro h_upper
                            exact vowel_upper_transform c (by simp [isVowel, h]) h_upper
                          · intro h_lower
                            exact vowel_lower_transform c (by simp [isVowel, h]) h_lower
                        | inr h => 
                          simp [h]; constructor
                          · intro h_upper
                            exact vowel_upper_transform c (by simp [isVowel, h]) h_upper
                          · intro h_lower
                            exact vowel_lower_transform c (by simp [isVowel, h]) h_lower
      · simp; constructor
        · intro h_upper
          exact non_vowel_upper_transform c h_vowel h_upper
        · intro h_lower
          exact non_vowel_lower_transform c h_vowel h_lower