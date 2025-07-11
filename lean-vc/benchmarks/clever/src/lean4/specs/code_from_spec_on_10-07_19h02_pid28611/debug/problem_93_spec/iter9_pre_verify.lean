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
lemma option_map_get_eq (f : Char → Char) (l : List Char) (i : ℕ) (h : i < l.length) : 
  (Option.map f l[i]?).getD 'A' = f (l[i]?.getD 'A') := by
  simp [List.get?_eq_getElem?]
  rw [List.getElem?_lt _ h]
  simp

-- LLM HELPER
lemma char_ofNat_val (n : ℕ) (h : n.isValidChar) : (Char.ofNatAux n h).val.toNat = n := by
  simp [Char.ofNatAux]

-- LLM HELPER
lemma char_val_add_2_valid (c : Char) : (c.val.toNat + 2).isValidChar := by
  unfold Nat.isValidChar
  have h : c.val.toNat < 0xD800 := by
    have : c.val.toNat ≤ 0x10FFFF := Char.val_le_1114111 c
    omega
  omega

-- LLM HELPER
lemma transform_vowel_upper (c : Char) (h_vowel : isVowel c = true) (h_upper : c.isUpper = true) :
  (transformChar c).val.toNat = c.toLower.val.toNat + 2 := by
  unfold transformChar
  simp [h_vowel, h_upper]
  have h_valid : (c.toLower.val.toNat + 2).isValidChar := char_val_add_2_valid c.toLower
  rw [char_ofNat_val _ h_valid]

-- LLM HELPER
lemma transform_vowel_lower (c : Char) (h_vowel : isVowel c = true) (h_lower : c.isLower = true) :
  (transformChar c).val.toNat = c.toUpper.val.toNat + 2 := by
  unfold transformChar
  simp [h_vowel, h_lower]
  have h_valid : (c.toUpper.val.toNat + 2).isValidChar := char_val_add_2_valid c.toUpper
  rw [char_ofNat_val _ h_valid]

-- LLM HELPER
lemma transform_non_vowel_upper (c : Char) (h_vowel : isVowel c = false) (h_upper : c.isUpper = true) :
  transformChar c = c.toLower := by
  unfold transformChar
  simp [h_vowel, h_upper]

-- LLM HELPER
lemma transform_non_vowel_lower (c : Char) (h_vowel : isVowel c = false) (h_lower : c.isLower = true) :
  transformChar c = c.toUpper := by
  unfold transformChar
  simp [h_vowel, h_lower]

-- LLM HELPER
lemma isVowel_cases (c : Char) : 
  isVowel c = true ↔ 
  (c = 'a' ∨ c = 'e' ∨ c = 'i' ∨ c = 'o' ∨ c = 'u' ∨ c = 'A' ∨ c = 'E' ∨ c = 'I' ∨ c = 'O' ∨ c = 'U') := by
  constructor
  · intro h
    unfold isVowel at h
    split at h <;> simp
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
lemma char_upper_lower_exclusive (c : Char) : c.isUpper = true → c.isLower = false := by
  intro h
  by_contra h_contra
  simp at h_contra
  have : c.isUpper = false := Char.isUpper_eq_false_iff_isLower_or_not_isAlpha.mpr (Or.inl h_contra)
  rw [this] at h
  simp at h

-- LLM HELPER
lemma char_lower_upper_exclusive (c : Char) : c.isLower = true → c.isUpper = false := by
  intro h
  by_contra h_contra
  simp at h_contra
  have : c.isLower = false := Char.isLower_eq_false_iff_isUpper_or_not_isAlpha.mpr (Or.inl h_contra)
  rw [this] at h
  simp at h

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
      · -- vowel case
        rw [isVowel_cases] at h_vowel
        cases h_vowel with
        | inl h => -- c = 'a'
          simp [h]
          constructor
          · intro h_upper
            rw [transform_vowel_upper c (by simp [isVowel, h]) h_upper]
            simp [h]
          · intro h_lower
            rw [transform_vowel_lower c (by simp [isVowel, h]) h_lower]
            simp [h]
        | inr h => cases h with
          | inl h => -- c = 'e'
            simp [h]
            constructor
            · intro h_upper
              rw [transform_vowel_upper c (by simp [isVowel, h]) h_upper]
              simp [h]
            · intro h_lower
              rw [transform_vowel_lower c (by simp [isVowel, h]) h_lower]
              simp [h]
          | inr h => cases h with
            | inl h => -- c = 'i'
              simp [h]
              constructor
              · intro h_upper
                rw [transform_vowel_upper c (by simp [isVowel, h]) h_upper]
                simp [h]
              · intro h_lower
                rw [transform_vowel_lower c (by simp [isVowel, h]) h_lower]
                simp [h]
            | inr h => cases h with
              | inl h => -- c = 'o'
                simp [h]
                constructor
                · intro h_upper
                  rw [transform_vowel_upper c (by simp [isVowel, h]) h_upper]
                  simp [h]
                · intro h_lower
                  rw [transform_vowel_lower c (by simp [isVowel, h]) h_lower]
                  simp [h]
              | inr h => cases h with
                | inl h => -- c = 'u'
                  simp [h]
                  constructor
                  · intro h_upper
                    rw [transform_vowel_upper c (by simp [isVowel, h]) h_upper]
                    simp [h]
                  · intro h_lower
                    rw [transform_vowel_lower c (by simp [isVowel, h]) h_lower]
                    simp [h]
                | inr h => cases h with
                  | inl h => -- c = 'A'
                    simp [h]
                    constructor
                    · intro h_upper
                      rw [transform_vowel_upper c (by simp [isVowel, h]) h_upper]
                      simp [h]
                    · intro h_lower
                      rw [transform_vowel_lower c (by simp [isVowel, h]) h_lower]
                      simp [h]
                  | inr h => cases h with
                    | inl h => -- c = 'E'
                      simp [h]
                      constructor
                      · intro h_upper
                        rw [transform_vowel_upper c (by simp [isVowel, h]) h_upper]
                        simp [h]
                      · intro h_lower
                        rw [transform_vowel_lower c (by simp [isVowel, h]) h_lower]
                        simp [h]
                    | inr h => cases h with
                      | inl h => -- c = 'I'
                        simp [h]
                        constructor
                        · intro h_upper
                          rw [transform_vowel_upper c (by simp [isVowel, h]) h_upper]
                          simp [h]
                        · intro h_lower
                          rw [transform_vowel_lower c (by simp [isVowel, h]) h_lower]
                          simp [h]
                      | inr h => cases h with
                        | inl h => -- c = 'O'
                          simp [h]
                          constructor
                          · intro h_upper
                            rw [transform_vowel_upper c (by simp [isVowel, h]) h_upper]
                            simp [h]
                          · intro h_lower
                            rw [transform_vowel_lower c (by simp [isVowel, h]) h_lower]
                            simp [h]
                        | inr h => -- c = 'U'
                          simp [h]
                          constructor
                          · intro h_upper
                            rw [transform_vowel_upper c (by simp [isVowel, h]) h_upper]
                            simp [h]
                          · intro h_lower
                            rw [transform_vowel_lower c (by simp [isVowel, h]) h_lower]
                            simp [h]
      · -- non-vowel case
        have h_not_vowel : ¬(c = 'a' ∨ c = 'e' ∨ c = 'i' ∨ c = 'o' ∨ c = 'u' ∨ c = 'A' ∨ c = 'E' ∨ c = 'I' ∨ c = 'O' ∨ c = 'U') := by
          rw [← isVowel_cases]
          exact h_vowel
        push_neg at h_not_vowel
        simp [h_not_vowel]
        constructor
        · intro h_upper
          rw [transform_non_vowel_upper c h_vowel h_upper]
        · intro h_lower
          rw [transform_non_vowel_lower c h_vowel h_lower]