import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def swapchar (c : Char) : Char :=
  if c.isLower then c.toUpper
  else if c.isUpper then c.toLower
  else c

-- LLM HELPER
def swapcase_string (s : String) : String :=
  String.mk (s.data.map swapchar)

/-- Return element-wise a copy of the string with uppercase characters converted to lowercase and vice versa -/
def swapcase {n : Nat} (a : Vector String n) : Id (Vector String n) :=
  return Vector.map swapcase_string a

-- LLM HELPER
lemma swapchar_involutive (c : Char) : swapchar (swapchar c) = c := by
  simp [swapchar]
  by_cases h1 : c.isLower
  · simp [h1]
    have : ¬c.toUpper.isLower := Char.not_isLower_toUpper c
    simp [this]
    exact Char.toLower_toUpper c
  · by_cases h2 : c.isUpper
    · simp [h1, h2]
      have : ¬c.toLower.isUpper := Char.not_isUpper_toLower c
      simp [this]
      exact Char.toUpper_toLower c
    · simp [h1, h2]

-- LLM HELPER
lemma swapcase_string_length (s : String) : (swapcase_string s).length = s.length := by
  simp [swapcase_string, String.length]

-- LLM HELPER
lemma swapcase_string_get (s : String) (i : Nat) (h : i < s.length) :
    (swapcase_string s).get? ⟨i⟩ = some (swapchar (s.get ⟨i, h⟩)) := by
  simp [swapcase_string, String.get?, String.get]
  rw [List.get?_map]
  simp [String.get]

-- LLM HELPER
lemma swapcase_string_empty : swapcase_string "" = "" := by
  simp [swapcase_string]

-- LLM HELPER
lemma swapcase_string_involutive (s : String) : swapcase_string (swapcase_string s) = s := by
  simp [swapcase_string]
  congr 1
  ext c
  simp [swapchar_involutive]

/-- Specification: numpy.strings.swapcase returns a vector where each string element
    has its case swapped (uppercase becomes lowercase and vice versa).

    Mathematical Properties:
    1. Element-wise correctness: Each element has its alphabetic characters case-swapped
    2. Length preservation: Each transformed string has the same length as the original
    3. Case transformation: Uppercase→lowercase, lowercase→uppercase, non-alpha unchanged
    4. Involutive property: swapcase(swapcase(x)) = x
    5. Empty string handling: Empty strings remain empty
    6. Character-level correctness: Each character is correctly transformed

    Precondition: True (no special preconditions for case swapping)
    Postcondition: For all indices i, result[i] is the case-swapped version of a[i]
-/
theorem swapcase_spec {n : Nat} (a : Vector String n) :
    ⦃⌜True⌝⦄
    swapcase a
    ⦃⇓r => ⌜∀ i : Fin n, 
      let original := a.get i
      let result := r.get i
      -- Length preservation: result has same length as original
      (result.length = original.length) ∧
      -- Empty string case: empty input produces empty output
      (original.length = 0 → result = "") ∧
      -- Character-level transformation: each character is correctly converted
      (∀ j : Nat, j < original.length → 
        ∃ origChar : Char, 
          original.get? ⟨j⟩ = some origChar ∧ 
          result.get? ⟨j⟩ = some (if origChar.isLower then origChar.toUpper 
                                    else if origChar.isUpper then origChar.toLower 
                                    else origChar)) ∧
      -- Involutive property: applying swapcase twice gives original string
      (∀ j : Nat, j < original.length → 
        ∃ origChar : Char, 
          original.get? ⟨j⟩ = some origChar ∧ 
          let swappedOnce := if origChar.isLower then origChar.toUpper 
                           else if origChar.isUpper then origChar.toLower 
                           else origChar
          let swappedTwice := if swappedOnce.isLower then swappedOnce.toUpper 
                             else if swappedOnce.isUpper then swappedOnce.toLower 
                             else swappedOnce
          swappedTwice = origChar) ∧
      -- Case transformation specifics
      (∀ j : Nat, j < original.length → 
        ∃ origChar : Char, 
          original.get? ⟨j⟩ = some origChar ∧ 
          (origChar.isLower → result.get? ⟨j⟩ = some origChar.toUpper) ∧
          (origChar.isUpper → result.get? ⟨j⟩ = some origChar.toLower) ∧
          (¬origChar.isAlpha → result.get? ⟨j⟩ = some origChar))⌝⦄ := by
  simp [swapcase]
  intro i
  simp [Vector.get_map]
  let original := a.get i
  let result := swapcase_string original
  constructor
  · exact swapcase_string_length original
  constructor
  · intro h
    simp [result]
    have : original = "" := by
      cases' original with data
      simp [String.length] at h
      simp [h]
    rw [this]
    exact swapcase_string_empty
  constructor
  · intro j hj
    use original.get ⟨j, hj⟩
    constructor
    · simp [String.get?]
    · rw [swapcase_string_get]
      simp [swapchar]
  constructor
  · intro j hj
    use original.get ⟨j, hj⟩
    constructor
    · simp [String.get?]
    · have char_eq := swapchar_involutive (original.get ⟨j, hj⟩)
      simp [swapchar] at char_eq
      exact char_eq
  · intro j hj
    use original.get ⟨j, hj⟩
    constructor
    · simp [String.get?]
    · rw [swapcase_string_get]
      simp [swapchar]
      constructor
      · intro h
        simp [h]
      constructor
      · intro h
        simp [h]
      · intro h
        simp [h]