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
  let result := String.mk (s.data.map transformChar)
  let h_result : i < result.length := by simp [String.length, String.mk]; exact h
  result.get ⟨i, h_result⟩ = transformChar (s.get ⟨i, h⟩) := by
  simp [String.get, String.mk]
  rw [List.get_map]

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
      let result := String.mk (s.data.map transformChar)
      let h_result : i < result.length := by
        rw [string_length_map]
        exact h_i
      let c := s.get ⟨i, h_i⟩
      let c' := result.get ⟨i, h_result⟩
      
      have h_transform : c' = transformChar c := by
        exact string_get_map s i h_i
      
      cases' Decidable.em (isVowel c) with h_vowel h_not_vowel
      · -- c is a vowel
        rw [isVowel_match] at h_vowel
        have vowel_cases : c = 'a' ∨ c = 'e' ∨ c = 'i' ∨ c = 'o' ∨ c = 'u' ∨ c = 'A' ∨ c = 'E' ∨ c = 'I' ∨ c = 'O' ∨ c = 'U' := h_vowel
        
        cases vowel_cases with
        | inl h_a => 
          simp [h_a]
          constructor
          · intro h_upper
            have h_lower : c.isLower = true := by simp [c, h_a, Char.isLower]
            simp [c, h_a] at h_upper
          · intro h_lower
            simp [c, h_a, Char.isUpper] at h_lower
        | inr h_rest =>
          cases h_rest with
          | inl h_e =>
            simp [h_e]
            constructor
            · intro h_upper
              simp [c, h_e, Char.isUpper] at h_upper
            · intro h_lower
              simp [c, h_e, Char.isLower] at h_lower
          | inr h_rest2 =>
            cases h_rest2 with
            | inl h_i_char =>
              simp [h_i_char]
              constructor
              · intro h_upper
                simp [c, h_i_char, Char.isUpper] at h_upper
              · intro h_lower
                simp [c, h_i_char, Char.isLower] at h_lower
            | inr h_rest3 =>
              cases h_rest3 with
              | inl h_o =>
                simp [h_o]
                constructor
                · intro h_upper
                  simp [c, h_o, Char.isUpper] at h_upper
                · intro h_lower
                  simp [c, h_o, Char.isLower] at h_lower
              | inr h_rest4 =>
                cases h_rest4 with
                | inl h_u =>
                  simp [h_u]
                  constructor
                  · intro h_upper
                    simp [c, h_u, Char.isUpper] at h_upper
                  · intro h_lower
                    simp [c, h_u, Char.isLower] at h_lower
                | inr h_rest5 =>
                  cases h_rest5 with
                  | inl h_A =>
                    simp [h_A]
                    constructor
                    · intro h_upper
                      rw [h_transform]
                      simp [transformChar, isVowel, h_A, Char.isUpper]
                      simp [Char.val, Char.ofNat, Char.toLower]
                    · intro h_lower
                      simp [c, h_A, Char.isLower] at h_lower
                  | inr h_rest6 =>
                    cases h_rest6 with
                    | inl h_E =>
                      simp [h_E]
                      constructor
                      · intro h_upper
                        rw [h_transform]
                        simp [transformChar, isVowel, h_E, Char.isUpper]
                        simp [Char.val, Char.ofNat, Char.toLower]
                      · intro h_lower
                        simp [c, h_E, Char.isLower] at h_lower
                    | inr h_rest7 =>
                      cases h_rest7 with
                      | inl h_I =>
                        simp [h_I]
                        constructor
                        · intro h_upper
                          rw [h_transform]
                          simp [transformChar, isVowel, h_I, Char.isUpper]
                          simp [Char.val, Char.ofNat, Char.toLower]
                        · intro h_lower
                          simp [c, h_I, Char.isLower] at h_lower
                      | inr h_rest8 =>
                        cases h_rest8 with
                        | inl h_O =>
                          simp [h_O]
                          constructor
                          · intro h_upper
                            rw [h_transform]
                            simp [transformChar, isVowel, h_O, Char.isUpper]
                            simp [Char.val, Char.ofNat, Char.toLower]
                          · intro h_lower
                            simp [c, h_O, Char.isLower] at h_lower
                        | inr h_U =>
                          simp [h_U]
                          constructor
                          · intro h_upper
                            rw [h_transform]
                            simp [transformChar, isVowel, h_U, Char.isUpper]
                            simp [Char.val, Char.ofNat, Char.toLower]
                          · intro h_lower
                            simp [c, h_U, Char.isLower] at h_lower
      · -- c is not a vowel
        simp
        constructor
        · intro h_upper
          rw [h_transform]
          simp [transformChar, isVowel_match] at h_not_vowel ⊢
          simp [h_not_vowel, h_upper]
        · intro h_lower
          rw [h_transform]
          simp [transformChar, isVowel_match] at h_not_vowel ⊢
          simp [h_not_vowel]
          have h_not_upper : c.isUpper = false := Char.not_isUpper_of_isLower h_lower
          simp [h_not_upper]