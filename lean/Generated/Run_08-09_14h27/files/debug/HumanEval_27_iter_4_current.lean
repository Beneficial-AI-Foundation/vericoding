/- 
function_signature: "def flip_case(string: str) -> str"
docstring: |
    For a given string, flip lowercase characters to uppercase and uppercase to lowercase.
test_cases:
  - input: "Hello"
    expected_output: "hELLO"
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def flip_char (c : Char) : Char :=
  if c.isLower then c.toUpper
  else if c.isUpper then c.toLower
  else c

def implementation (string: String) : String :=
  String.mk (string.toList.map flip_char)

def problem_spec
-- function signature
(implementation: String → String)
-- inputs
(string: String) :=
-- spec
let spec (result: String) :=
let chars_in_result := result.toList;
let chars_in_string := string.toList;
chars_in_result.length = string.length ∧
(∀ i, i < chars_in_result.length →
  let c := chars_in_result[i]!;
  let c' := chars_in_string[i]!;
  (c.isUpper → c'.isLower) ∧
  (c.isLower → c'.isUpper) ∧
  ((¬ c.isUpper ∧ ¬ c.isLower) → c = c')
);
-- program termination
∃ result, implementation string = result ∧
spec result

-- LLM HELPER
lemma flip_char_upper (c : Char) (h : c.isUpper) : (flip_char c).isLower := by
  unfold flip_char
  have h_not_lower : ¬c.isLower := Char.not_isLower_of_isUpper h
  simp [h_not_lower, h]

-- LLM HELPER
lemma flip_char_lower (c : Char) (h : c.isLower) : (flip_char c).isUpper := by
  unfold flip_char
  simp [h]

-- LLM HELPER
lemma flip_char_neither (c : Char) (h : ¬c.isUpper ∧ ¬c.isLower) : flip_char c = c := by
  unfold flip_char
  simp [h.1, h.2]

-- LLM HELPER
lemma string_mk_toList_length (chars : List Char) : (String.mk chars).toList.length = chars.length := by
  simp [String.toList]

-- LLM HELPER  
lemma string_mk_toList_get (chars : List Char) (i : Nat) (h : i < chars.length) :
  (String.mk chars).toList[i]! = chars[i]! := by
  simp [String.toList]

-- LLM HELPER
lemma char_isUpper_isAlpha (c : Char) (h : c.isUpper = true) : c.isAlpha = true := by
  exact Char.isAlpha_of_isUpper (Bool.eq_true_iff.mp h)

-- LLM HELPER
lemma char_isLower_isAlpha (c : Char) (h : c.isLower = true) : c.isAlpha = true := by
  exact Char.isAlpha_of_isLower (Bool.eq_true_iff.mp h)

theorem correctness
(string: String)
: problem_spec implementation string
:= by
  unfold problem_spec implementation
  let result := String.mk (string.toList.map flip_char)
  use result
  constructor
  · rfl
  · let chars_in_result := result.toList
    let chars_in_string := string.toList
    constructor
    · simp [chars_in_result, result]
      rw [string_mk_toList_length, List.length_map]
      simp [String.length, chars_in_string]
    · intro i hi
      let c := chars_in_result[i]!
      let c' := chars_in_string[i]!
      simp [result]
      have c_eq : c = (string.toList.map flip_char)[i]! := by
        simp [c, chars_in_result, result, string_mk_toList_get]
      rw [c_eq]
      have c_def : (string.toList.map flip_char)[i]! = flip_char (string.toList[i]!) := by
        rw [List.getElem!_map]
      rw [c_def]
      have c'_eq : c' = string.toList[i]! := by simp [c']
      rw [c'_eq]
      let orig_char := string.toList[i]!
      constructor
      · intro h_upper
        have flipped_upper : (flip_char orig_char).isUpper := h_upper
        by_cases h1 : orig_char.isLower
        · have : flip_char orig_char = orig_char.toUpper := by simp [flip_char, h1]
          rw [this] at flipped_upper
          exact h1
        · by_cases h2 : orig_char.isUpper
          · have : flip_char orig_char = orig_char.toLower := by
              simp [flip_char, h2, Char.not_isLower_of_isUpper h2]
            rw [this] at flipped_upper
            have : orig_char.toLower.isUpper = false := by simp
            rw [this] at flipped_upper
            simp at flipped_upper
          · have : flip_char orig_char = orig_char := by simp [flip_char, h1, h2]
            rw [this] at flipped_upper
            contradiction
      · constructor
        · intro h_lower
          have flipped_lower : (flip_char orig_char).isLower := h_lower
          by_cases h1 : orig_char.isUpper
          · have : flip_char orig_char = orig_char.toLower := by
              simp [flip_char, h1, Char.not_isLower_of_isUpper h1]
            rw [this] at flipped_lower
            exact h1
          · by_cases h2 : orig_char.isLower
            · have : flip_char orig_char = orig_char.toUpper := by simp [flip_char, h2]
              rw [this] at flipped_lower
              have : orig_char.toUpper.isLower = false := by simp
              rw [this] at flipped_lower
              simp at flipped_lower
            · have : flip_char orig_char = orig_char := by simp [flip_char, h1, h2]
              rw [this] at flipped_lower
              contradiction
        · intro h_neither
          have : flip_char orig_char = orig_char := flip_char_neither orig_char h_neither
          exact this

-- #test implementation "Hello" = "hELLO"