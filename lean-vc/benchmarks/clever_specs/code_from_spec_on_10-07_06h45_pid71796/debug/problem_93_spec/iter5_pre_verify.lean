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
    let c := s.get ⟨i, by simp [String.length] at *; exact Nat.lt_of_lt_of_le i (by assumption) s.data.length_le⟩;
    let c' := result.get ⟨i, by simp [String.length] at *; exact Nat.lt_of_lt_of_le i (by assumption) result.data.length_le⟩;
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
  c = 'a' || c = 'e' || c = 'i' || c = 'o' || c = 'u' ||
  c = 'A' || c = 'E' || c = 'I' || c = 'O' || c = 'U'

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
  String.mk (s.data.map transformChar)

-- LLM HELPER
lemma string_length_map (s : String) : 
  (String.mk (s.data.map transformChar)).length = s.length := by
  simp [String.length, String.mk]

-- LLM HELPER
lemma string_get_map (s : String) (i : Nat) (h : i < s.length) :
  (String.mk (s.data.map transformChar)).get ⟨i, by simp [String.length, String.mk]; exact h⟩ = transformChar (s.get ⟨i, h⟩) := by
  simp [String.get, String.mk]
  rw [List.get_map]

-- LLM HELPER
lemma transformChar_vowel_upper (c : Char) (h_vowel : isVowel c = true) (h_upper : c.isUpper = true) :
  (transformChar c).val = c.toLower.val + 2 := by
  simp [transformChar, h_vowel, h_upper]
  simp [Char.val, Char.ofNat]

-- LLM HELPER
lemma transformChar_vowel_lower (c : Char) (h_vowel : isVowel c = true) (h_lower : c.isLower = true) :
  (transformChar c).val = c.toUpper.val + 2 := by
  simp [transformChar, h_vowel]
  rw [if_neg]
  simp [Char.val, Char.ofNat]
  exact Char.not_isUpper_of_isLower h_lower

-- LLM HELPER
lemma transformChar_non_vowel_upper (c : Char) (h_vowel : isVowel c = false) (h_upper : c.isUpper = true) :
  transformChar c = c.toLower := by
  simp [transformChar, h_vowel, h_upper]

-- LLM HELPER
lemma transformChar_non_vowel_lower (c : Char) (h_vowel : isVowel c = false) (h_lower : c.isLower = true) :
  transformChar c = c.toUpper := by
  simp [transformChar, h_vowel]
  rw [if_neg]
  simp [h_lower]
  exact Char.not_isUpper_of_isLower h_lower

-- LLM HELPER
lemma isVowel_match (c : Char) : 
  isVowel c = true ↔ 
  (c = 'a' ∨ c = 'e' ∨ c = 'i' ∨ c = 'o' ∨ c = 'u' ∨ 
   c = 'A' ∨ c = 'E' ∨ c = 'I' ∨ c = 'O' ∨ c = 'U') := by
  simp [isVowel]

theorem correctness
(s: String)
: problem_spec implementation s := by
  simp [problem_spec]
  use String.mk (s.data.map transformChar)
  constructor
  · rfl
  · intro h_alpha
    constructor
    · exact string_length_map s
    · intro i h_i
      have h_result : i < (String.mk (s.data.map transformChar)).length := by
        rw [string_length_map]
        exact h_i
      rw [string_get_map s i h_i]
      let c := s.get ⟨i, h_i⟩
      let c' := transformChar c
      cases' Decidable.em (isVowel c) with h_vowel h_not_vowel
      · -- c is a vowel
        rw [isVowel_match] at h_vowel
        simp only [c]
        have vowel_cases : c = 'a' ∨ c = 'e' ∨ c = 'i' ∨ c = 'o' ∨ c = 'u' ∨ c = 'A' ∨ c = 'E' ∨ c = 'I' ∨ c = 'O' ∨ c = 'U' := h_vowel
        cases vowel_cases with
        | inl h_a => 
          simp [h_a]
          constructor
          · intro h_upper
            have : c.isLower = true := by simp [c, h_a, Char.isLower]
            rw [transformChar_vowel_lower c (by simp [isVowel, h_a]) this]
            simp [c, h_a]
          · intro h_lower
            rw [transformChar_vowel_upper c (by simp [isVowel, h_a]) (by simp [c, h_a, Char.isUpper])]
            simp [c, h_a]
        | inr h_rest =>
          cases h_rest with
          | inl h_e =>
            simp [h_e]
            constructor
            · intro h_upper
              have : c.isLower = true := by simp [c, h_e, Char.isLower]
              rw [transformChar_vowel_lower c (by simp [isVowel, h_e]) this]
              simp [c, h_e]
            · intro h_lower
              rw [transformChar_vowel_upper c (by simp [isVowel, h_e]) (by simp [c, h_e, Char.isUpper])]
              simp [c, h_e]
          | inr h_rest2 =>
            cases h_rest2 with
            | inl h_i =>
              simp [h_i]
              constructor
              · intro h_upper
                have : c.isLower = true := by simp [c, h_i, Char.isLower]
                rw [transformChar_vowel_lower c (by simp [isVowel, h_i]) this]
                simp [c, h_i]
              · intro h_lower
                rw [transformChar_vowel_upper c (by simp [isVowel, h_i]) (by simp [c, h_i, Char.isUpper])]
                simp [c, h_i]
            | inr h_rest3 =>
              cases h_rest3 with
              | inl h_o =>
                simp [h_o]
                constructor
                · intro h_upper
                  have : c.isLower = true := by simp [c, h_o, Char.isLower]
                  rw [transformChar_vowel_lower c (by simp [isVowel, h_o]) this]
                  simp [c, h_o]
                · intro h_lower
                  rw [transformChar_vowel_upper c (by simp [isVowel, h_o]) (by simp [c, h_o, Char.isUpper])]
                  simp [c, h_o]
              | inr h_rest4 =>
                cases h_rest4 with
                | inl h_u =>
                  simp [h_u]
                  constructor
                  · intro h_upper
                    have : c.isLower = true := by simp [c, h_u, Char.isLower]
                    rw [transformChar_vowel_lower c (by simp [isVowel, h_u]) this]
                    simp [c, h_u]
                  · intro h_lower
                    rw [transformChar_vowel_upper c (by simp [isVowel, h_u]) (by simp [c, h_u, Char.isUpper])]
                    simp [c, h_u]
                | inr h_rest5 =>
                  cases h_rest5 with
                  | inl h_A =>
                    simp [h_A]
                    constructor
                    · intro h_upper
                      rw [transformChar_vowel_upper c (by simp [isVowel, h_A]) (by simp [c, h_A, Char.isUpper])]
                      simp [c, h_A]
                    · intro h_lower
                      have : c.isLower = false := by simp [c, h_A, Char.isLower]
                      contradiction
                  | inr h_rest6 =>
                    cases h_rest6 with
                    | inl h_E =>
                      simp [h_E]
                      constructor
                      · intro h_upper
                        rw [transformChar_vowel_upper c (by simp [isVowel, h_E]) (by simp [c, h_E, Char.isUpper])]
                        simp [c, h_E]
                      · intro h_lower
                        have : c.isLower = false := by simp [c, h_E, Char.isLower]
                        contradiction
                    | inr h_rest7 =>
                      cases h_rest7 with
                      | inl h_I =>
                        simp [h_I]
                        constructor
                        · intro h_upper
                          rw [transformChar_vowel_upper c (by simp [isVowel, h_I]) (by simp [c, h_I, Char.isUpper])]
                          simp [c, h_I]
                        · intro h_lower
                          have : c.isLower = false := by simp [c, h_I, Char.isLower]
                          contradiction
                      | inr h_rest8 =>
                        cases h_rest8 with
                        | inl h_O =>
                          simp [h_O]
                          constructor
                          · intro h_upper
                            rw [transformChar_vowel_upper c (by simp [isVowel, h_O]) (by simp [c, h_O, Char.isUpper])]
                            simp [c, h_O]
                          · intro h_lower
                            have : c.isLower = false := by simp [c, h_O, Char.isLower]
                            contradiction
                        | inr h_U =>
                          simp [h_U]
                          constructor
                          · intro h_upper
                            rw [transformChar_vowel_upper c (by simp [isVowel, h_U]) (by simp [c, h_U, Char.isUpper])]
                            simp [c, h_U]
                          · intro h_lower
                            have : c.isLower = false := by simp [c, h_U, Char.isLower]
                            contradiction
      · -- c is not a vowel
        simp
        constructor
        · intro h_upper
          rw [transformChar_non_vowel_upper c (by simp [isVowel_match] at h_not_vowel; exact h_not_vowel) h_upper]
        · intro h_lower
          rw [transformChar_non_vowel_lower c (by simp [isVowel_match] at h_not_vowel; exact h_not_vowel) h_lower]