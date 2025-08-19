import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.strings.title",
  "category": "String transformation",
  "description": "Return element-wise title cased version of string or unicode",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.strings.title.html",
  "doc": "Return element-wise title cased version of string or unicode.\n\nTitle case words start with uppercase characters, all remaining cased characters are lowercase.\n\nFor byte strings, this method is locale-dependent.\n\nParameters\n----------\na : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype\n    Input array\n\nReturns\n-------\nout : ndarray\n    Output array of \`StringDType\`, \`bytes_\` or \`str_\` dtype,\n    depending on input type",
  "code": "def title(a):\n    \"\"\"\n    Return element-wise title cased version of string or unicode.\n\n    Title case words start with uppercase characters, all remaining cased\n    characters are lowercase.\n\n    For byte strings, this method is locale-dependent.\n\n    Parameters\n    ----------\n    a : array_like, with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype\n        Input array\n\n    Returns\n    -------\n    out : ndarray\n        Output array of \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype,\n        depending on input type\n\n    See Also\n    --------\n    str.title\n\n    Examples\n    --------\n    >>> c=np.array(['a1b c','1b ca','b ca1','ca1b'],'S5'); c\n    array([b'a1b c', b'1b ca', b'b ca1', b'ca1b'],\n          dtype='|S5')\n    >>> np.strings.title(c)\n    array([b'A1B C', b'1B Ca', b'B Ca1', b'Ca1B'],\n          dtype='|S5')\n\n    \"\"\"\n    a = np.asanyarray(a)\n    if not _is_string_dtype(a.dtype):\n        raise TypeError(\"string operation on non-string array\")\n    return _title_ufunc(a)"
}
-/

/-- numpy.strings.title: Return element-wise title cased version of string or unicode.

    Converts each string element in the input vector to title case. Title case means
    the first character of each word is uppercase and all other cased characters are
    lowercase. Words are typically separated by whitespace or non-alphabetic characters.

    The function preserves the shape of the input array and handles empty strings
    appropriately by returning them unchanged.

    From NumPy documentation:
    - Parameters: a (array_like) - Input array with string dtype
    - Returns: out (ndarray) - Output array with elements converted to title case

    Mathematical Properties:
    1. Element-wise transformation: result[i] = title(a[i]) for all i
    2. Length preservation: result[i].length = a[i].length for all i
    3. Title case transformation: first letter of each word uppercase, others lowercase
    4. Word boundary detection: non-alphabetic characters separate words
    5. Preserves vector length: result.size = a.size
-/

-- Helper function to check if a character is at the start of a word.
-- A character is at the start of a word if it's alphabetic and either:
-- 1. It's the first character in the string, or
-- 2. The previous character is not alphabetic
def isWordStart (s : String) (pos : Nat) : Bool :=
  if pos = 0 then true
  else
    match s.get? ⟨pos⟩ with
    | none => false
    | some c => 
      if c.isAlpha then
        match s.get? ⟨pos - 1⟩ with
        | none => true
        | some prevChar => ¬prevChar.isAlpha
      else false

-- Helper function to check if a character should be uppercase in title case.
-- A character should be uppercase if it's alphabetic and at the start of a word.
def shouldBeUpperInTitle (s : String) (pos : Nat) : Bool :=
  match s.get? ⟨pos⟩ with
  | none => false
  | some c => c.isAlpha ∧ isWordStart s pos

-- Helper function to convert a single string to title case
def titleString (s : String) : String :=
  let charsList := s.toList
  let indexedChars := charsList.zipIdx
  let titleChars := indexedChars.map fun (c, i) => 
    if shouldBeUpperInTitle s i then c.toUpper else c.toLower
  String.mk titleChars

def title {n : Nat} (a : Vector String n) : Id (Vector String n) :=
  pure (a.map titleString)

-- LLM HELPER
lemma string_get_eq_toList_get (s : String) (i : Nat) (hi : i < s.length) :
  s.get? ⟨i⟩ = s.toList.get? i := by
  rfl

-- LLM HELPER
lemma titleString_length (s : String) : (titleString s).length = s.length := by
  simp [titleString]
  rw [String.length_mk]
  simp [List.length_zipIdx]

-- LLM HELPER
lemma titleString_empty (s : String) : s.length = 0 → titleString s = "" := by
  intro h
  simp [titleString]
  rw [String.length_eq_zero] at h
  rw [h]
  rfl

-- LLM HELPER
lemma titleString_get_correct (s : String) (j : Nat) (hj : j < s.length) :
  ∃ origChar resultChar : Char,
    s.get? ⟨j⟩ = some origChar ∧ 
    (titleString s).get? ⟨j⟩ = some resultChar ∧
    (shouldBeUpperInTitle s j → resultChar = origChar.toUpper) ∧
    (¬shouldBeUpperInTitle s j ∧ origChar.isAlpha → resultChar = origChar.toLower) ∧
    (¬origChar.isAlpha → resultChar = origChar) := by
  simp [titleString]
  have h_get : s.get? ⟨j⟩ = some (s.toList.get ⟨j, by simp; exact hj⟩) := by
    simp
  use s.toList.get ⟨j, by simp; exact hj⟩
  have h_result : (String.mk (List.zipIdx s.toList).map fun (c, i) => 
    if shouldBeUpperInTitle s i then c.toUpper else c.toLower).get? ⟨j⟩ = 
    some (if shouldBeUpperInTitle s j then (s.toList.get ⟨j, by simp; exact hj⟩).toUpper 
          else (s.toList.get ⟨j, by simp; exact hj⟩).toLower) := by
    simp [String.get?, String.mk]
    rw [List.get?_map]
    simp [List.get?_zipIdx]
    simp [List.get?_eq_get]
  use if shouldBeUpperInTitle s j then (s.toList.get ⟨j, by simp; exact hj⟩).toUpper 
       else (s.toList.get ⟨j, by simp; exact hj⟩).toLower
  constructor
  · exact h_get
  constructor
  · exact h_result
  constructor
  · intro h_should
    simp [h_should]
  constructor
  · intro h_not_should h_alpha
    simp [h_not_should]
  · intro h_not_alpha
    simp [h_not_should]
    have : ¬shouldBeUpperInTitle s j := by
      simp [shouldBeUpperInTitle]
      right
      exact h_not_alpha
    simp [this]
    rw [Char.toLower_eq_iff]
    right
    exact h_not_alpha

-- LLM HELPER
lemma titleString_word_boundary (s : String) (j : Nat) (hj : j < s.length) (hj_pos : j > 0) :
  ∃ prevChar currChar resultChar : Char,
    s.get? ⟨j - 1⟩ = some prevChar ∧
    s.get? ⟨j⟩ = some currChar ∧
    (titleString s).get? ⟨j⟩ = some resultChar ∧
    (¬prevChar.isAlpha ∧ currChar.isAlpha → resultChar = currChar.toUpper) := by
  have hj_pred : j - 1 < s.length := by omega
  use s.toList.get ⟨j - 1, by simp; exact hj_pred⟩
  use s.toList.get ⟨j, by simp; exact hj⟩
  use if shouldBeUpperInTitle s j then (s.toList.get ⟨j, by simp; exact hj⟩).toUpper 
       else (s.toList.get ⟨j, by simp; exact hj⟩).toLower
  constructor
  · simp
  constructor
  · simp
  constructor
  · simp [titleString]
    rw [String.get?, String.mk]
    rw [List.get?_map]
    simp [List.get?_zipIdx]
    simp [List.get?_eq_get]
  · intro h_boundary
    simp [shouldBeUpperInTitle, isWordStart]
    have : shouldBeUpperInTitle s j := by
      simp [shouldBeUpperInTitle, isWordStart]
      constructor
      · exact h_boundary.2
      · simp [hj_pos]
        exact h_boundary.1
    simp [this]

-- LLM HELPER
lemma titleString_first_char (s : String) (h_nonempty : s.length > 0) :
  ∃ firstChar : Char,
    s.get? ⟨0⟩ = some firstChar ∧
    (firstChar.isAlpha → 
      ∃ resultFirstChar : Char,
        (titleString s).get? ⟨0⟩ = some resultFirstChar ∧
        resultFirstChar = firstChar.toUpper) := by
  use s.toList.get ⟨0, by simp; exact h_nonempty⟩
  constructor
  · simp
  · intro h_alpha
    use if shouldBeUpperInTitle s 0 then (s.toList.get ⟨0, by simp; exact h_nonempty⟩).toUpper 
         else (s.toList.get ⟨0, by simp; exact h_nonempty⟩).toLower
    constructor
    · simp [titleString]
      rw [String.get?, String.mk]
      rw [List.get?_map]
      simp [List.get?_zipIdx]
      simp [List.get?_eq_get]
    · have : shouldBeUpperInTitle s 0 := by
        simp [shouldBeUpperInTitle, isWordStart]
        exact h_alpha
      simp [this]

/-- Specification: numpy.strings.title returns a vector where each string element
    is converted to title case.

    Mathematical Properties:
    1. Element-wise correctness: Each element is correctly converted to title case
    2. Length preservation: Each transformed string has the same length as the original
    3. Title case transformation: First letter of each word is uppercase, others lowercase
    4. Word boundary handling: Words separated by non-alphabetic characters
    5. Empty string handling: Empty strings remain empty

    Precondition: True (no special preconditions for title case conversion)
    Postcondition: For all indices i, result[i] is the title case version of a[i]
-/
theorem title_spec {n : Nat} (a : Vector String n) :
    ⦃⌜True⌝⦄
    title a
    ⦃⇓r => ⌜∀ i : Fin n, 
      let original := a.get i
      let result := r.get i
      -- Length preservation: result has same length as original
      (result.length = original.length) ∧
      -- Empty string case: empty input produces empty output
      (original.length = 0 → result = "") ∧
      -- Title case transformation: correct case for each character
      (∀ j : Nat, j < original.length → 
        ∃ origChar resultChar : Char, 
          original.get? ⟨j⟩ = some origChar ∧ 
          result.get? ⟨j⟩ = some resultChar ∧
          -- If character should be uppercase (word start), it is uppercase
          (shouldBeUpperInTitle original j → resultChar = origChar.toUpper) ∧
          -- If character should be lowercase (not word start but alphabetic), it is lowercase
          (¬shouldBeUpperInTitle original j ∧ origChar.isAlpha → resultChar = origChar.toLower) ∧
          -- Non-alphabetic characters remain unchanged
          (¬origChar.isAlpha → resultChar = origChar)) ∧
      -- Word boundary property: alphabetic chars after non-alphabetic are uppercase
      (∀ j : Nat, j < original.length → j > 0 →
        ∃ prevChar currChar resultChar : Char,
          original.get? ⟨j - 1⟩ = some prevChar ∧
          original.get? ⟨j⟩ = some currChar ∧
          result.get? ⟨j⟩ = some resultChar ∧
          (¬prevChar.isAlpha ∧ currChar.isAlpha → resultChar = currChar.toUpper)) ∧
      -- Sanity check: non-empty strings are properly title-cased
      (original.length > 0 →
        ∃ firstChar : Char,
          original.get? ⟨0⟩ = some firstChar ∧
          (firstChar.isAlpha → 
            ∃ resultFirstChar : Char,
              result.get? ⟨0⟩ = some resultFirstChar ∧
              resultFirstChar = firstChar.toUpper))⌝⦄ := by
  simp [title]
  intro i
  simp [Vector.get_map]
  let original := a.get i
  constructor
  · exact titleString_length original
  constructor
  · exact titleString_empty original
  constructor
  · intro j hj
    exact titleString_get_correct original j hj
  constructor
  · intro j hj hj_pos
    exact titleString_word_boundary original j hj hj_pos
  · intro h_nonempty
    exact titleString_first_char original h_nonempty