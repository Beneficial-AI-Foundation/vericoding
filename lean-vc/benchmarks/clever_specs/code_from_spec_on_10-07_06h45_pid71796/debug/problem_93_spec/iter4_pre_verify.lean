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
        cases' vowel_cases with h h
        · -- c = 'a'
          simp [h]
          constructor
          · intro h_upper
            have : c.isLower = true := by simp [c, h, Char.isLower]
            rw [transformChar_vowel_lower c (by simp [isVowel, h]) this]
            simp [c, h]
          · intro h_lower
            rw [transformChar_vowel_upper c (by simp [isVowel, h]) (by simp [c, h, Char.isUpper])]
            simp [c, h]
        · cases' h with h h
          · -- c = 'e'
            simp [h]
            constructor
            · intro h_upper
              have : c.isLower = true := by simp [c, h, Char.isLower]
              rw [transformChar_vowel_lower c (by simp [isVowel, h]) this]
              simp [c, h]
            · intro h_lower
              rw [transformChar_vowel_upper c (by simp [isVowel, h]) (by simp [c, h, Char.isUpper])]
              simp [c, h]
          · cases' h with h h
            · -- c = 'i'
              simp [h]
              constructor
              · intro h_upper
                have : c.isLower = true := by simp [c, h, Char.isLower]
                rw [transformChar_vowel_lower c (by simp [isVowel, h]) this]
                simp [c, h]
              · intro h_lower
                rw [transformChar_vowel_upper c (by simp [isVowel, h]) (by simp [c, h, Char.isUpper])]
                simp [c, h]
            · cases' h with h h
              · -- c = 'o'
                simp [h]
                constructor
                · intro h_upper
                  have : c.isLower = true := by simp [c, h, Char.isLower]
                  rw [transformChar_vowel_lower c (by simp [isVowel, h]) this]
                  simp [c, h]
                · intro h_lower
                  rw [transformChar_vowel_upper c (by simp [isVowel, h]) (by simp [c, h, Char.isUpper])]
                  simp [c, h]
              · cases' h with h h
                · -- c = 'u'
                  simp [h]
                  constructor
                  · intro h_upper
                    have : c.isLower = true := by simp [c, h, Char.isLower]
                    rw [transformChar_vowel_lower c (by simp [isVowel, h]) this]
                    simp [c, h]
                  · intro h_lower
                    rw [transformChar_vowel_upper c (by simp [isVowel, h]) (by simp [c, h, Char.isUpper])]
                    simp [c, h]
                · cases' h with h h
                  · -- c = 'A'
                    simp [h]
                    constructor
                    · intro h_upper
                      rw [transformChar_vowel_upper c (by simp [isVowel, h]) (by simp [c, h, Char.isUpper])]
                      simp [c, h]
                    · intro h_lower
                      have : c.isLower = false := by simp [c, h, Char.isLower]
                      contradiction
                  · cases' h with h h
                    · -- c = 'E'
                      simp [h]
                      constructor
                      · intro h_upper
                        rw [transformChar_vowel_upper c (by simp [isVowel, h]) (by simp [c, h, Char.isUpper])]
                        simp [c, h]
                      · intro h_lower
                        have : c.isLower = false := by simp [c, h, Char.isLower]
                        contradiction
                    · cases' h with h h
                      · -- c = 'I'
                        simp [h]
                        constructor
                        · intro h_upper
                          rw [transformChar_vowel_upper c (by simp [isVowel, h]) (by simp [c, h, Char.isUpper])]
                          simp [c, h]
                        · intro h_lower
                          have : c.isLower = false := by simp [c, h, Char.isLower]
                          contradiction
                      · cases' h with h h
                        · -- c = 'O'
                          simp [h]
                          constructor
                          · intro h_upper
                            rw [transformChar_vowel_upper c (by simp [isVowel, h]) (by simp [c, h, Char.isUpper])]
                            simp [c, h]
                          · intro h_lower
                            have : c.isLower = false := by simp [c, h, Char.isLower]
                            contradiction
                        · -- c = 'U'
                          simp [h]
                          constructor
                          · intro h_upper
                            rw [transformChar_vowel_upper c (by simp [isVowel, h]) (by simp [c, h, Char.isUpper])]
                            simp [c, h]
                          · intro h_lower
                            have : c.isLower = false := by simp [c, h, Char.isLower]
                            contradiction
      · -- c is not a vowel
        simp
        constructor
        · intro h_upper
          rw [transformChar_non_vowel_upper c (by simp [isVowel_match] at h_not_vowel; exact h_not_vowel) h_upper]
        · intro h_lower
          rw [transformChar_non_vowel_lower c (by simp [isVowel_match] at h_not_vowel; exact h_not_vowel) h_lower]