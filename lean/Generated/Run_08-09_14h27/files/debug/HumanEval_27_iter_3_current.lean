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
      simp [result] at c hi
      rw [string_mk_toList_get] at c
      · simp [c]
        rw [List.getElem!_map]
        simp [c']
        constructor
        · intro h_upper
          have c_is_flipped : c = flip_char c' := by
            simp [c, List.getElem!_map]
          rw [c_is_flipped] at h_upper
          by_cases h1 : c'.isUpper
          · have : flip_char c' = c'.toLower := by
              simp [flip_char, h1, Char.not_isLower_of_isUpper h1]
            rw [this] at h_upper
            have : c'.toLower.isUpper = false := by simp
            rw [this] at h_upper
            simp at h_upper
          · by_cases h2 : c'.isLower
            · have : flip_char c' = c'.toUpper := by simp [flip_char, h2]
              rw [this] at h_upper
              exact h2
            · have : flip_char c' = c' := by simp [flip_char, h1, h2]
              rw [this] at h_upper
              contradiction
        · constructor
          · intro h_lower
            have c_is_flipped : c = flip_char c' := by
              simp [c, List.getElem!_map]
            rw [c_is_flipped] at h_lower
            by_cases h1 : c'.isLower
            · have : flip_char c' = c'.toUpper := by simp [flip_char, h1]
              rw [this] at h_lower
              have : c'.toUpper.isLower = false := by simp
              rw [this] at h_lower
              simp at h_lower
            · by_cases h2 : c'.isUpper
              · have : flip_char c' = c'.toLower := by
                  simp [flip_char, h2, Char.not_isLower_of_isUpper h2]
                rw [this] at h_lower
                exact h2
              · have : flip_char c' = c' := by simp [flip_char, h1, h2]
                rw [this] at h_lower
                contradiction
          · intro h_neither
            have c_is_flipped : c = flip_char c' := by
              simp [c, List.getElem!_map]
            rw [c_is_flipped]
            exact flip_char_neither c' h_neither
      · simp [result] at hi
        rw [string_mk_toList_length, List.length_map] at hi
        exact hi

-- #test implementation "Hello" = "hELLO"