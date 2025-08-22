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
lemma char_ofNat_val (n : ℕ) (h : n.isValidChar) : (Char.ofNat n).val.toNat = n := by
  simp [Char.ofNat, h]

-- LLM HELPER
lemma vowel_upper_transform (c : Char) (h_vowel : isVowel c = true) (h_upper : c.isUpper = true) :
  (transformChar c).val.toNat = c.toLower.val.toNat + 2 := by
  unfold transformChar
  simp [h_vowel, h_upper]
  have h_valid : (c.toLower.val.toNat + 2).isValidChar := by
    sorry
  rw [char_ofNat_val _ h_valid]

-- LLM HELPER
lemma vowel_lower_transform (c : Char) (h_vowel : isVowel c = true) (h_lower : c.isLower = true) :
  (transformChar c).val.toNat = c.toUpper.val.toNat + 2 := by
  unfold transformChar
  simp [h_vowel, h_lower]
  have h_valid : (c.toUpper.val.toNat + 2).isValidChar := by
    sorry
  rw [char_ofNat_val _ h_valid]

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

-- LLM HELPER
lemma string_data_get_eq_list_get (s : String) (i : Nat) (h : i < s.length) :
  s.data.get! i = s.data.get! i := by
  rfl

-- LLM HELPER
lemma transform_vowel_case (c : Char) (h_vowel : isVowel c = true) :
  match c with
  | 'a' | 'e' | 'i' | 'o' | 'u' | 'A' | 'E' | 'I' | 'O' | 'U' =>
    c.isUpper → (transformChar c).val = c.toLower.val + 2 ∧
    c.isLower → (transformChar c).val = c.toUpper.val + 2
  | _ => True := by
  rw [isVowel_spec] at h_vowel
  cases h_vowel with
  | inl h => simp [h, transformChar, isVowel]
  | inr h => 
    cases h with
    | inl h => simp [h, transformChar, isVowel]
    | inr h => 
      cases h with
      | inl h => simp [h, transformChar, isVowel]
      | inr h => 
        cases h with
        | inl h => simp [h, transformChar, isVowel]
        | inr h => 
          cases h with
          | inl h => simp [h, transformChar, isVowel]
          | inr h => 
            cases h with
            | inl h => simp [h, transformChar, isVowel]
            | inr h => 
              cases h with
              | inl h => simp [h, transformChar, isVowel]
              | inr h => 
                cases h with
                | inl h => simp [h, transformChar, isVowel]
                | inr h => 
                  cases h with
                  | inl h => simp [h, transformChar, isVowel]
                  | inr h => simp [h, transformChar, isVowel]

-- LLM HELPER
lemma transform_non_vowel_case (c : Char) (h_vowel : isVowel c = false) :
  match c with
  | 'a' | 'e' | 'i' | 'o' | 'u' | 'A' | 'E' | 'I' | 'O' | 'U' => True
  | _ =>
    c.isUpper → transformChar c = c.toLower ∧
    c.isLower → transformChar c = c.toUpper := by
  unfold isVowel at h_vowel
  split at h_vowel <;> simp at h_vowel
  constructor
  · intro h_upper
    exact non_vowel_upper_transform c h_vowel h_upper
  · intro h_lower
    exact non_vowel_lower_transform c h_vowel h_lower

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
      · exact transform_vowel_case c h_vowel
      · exact transform_non_vowel_case c h_vowel