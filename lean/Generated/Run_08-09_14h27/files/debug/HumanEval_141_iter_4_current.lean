/- 
function_signature: "def file_name_check(file_name: str) -> str"
docstring: |
    Create a function which takes a string representing a file's name, and returns
    'Yes' if the the file's name is valid, and returns 'No' otherwise.
    A file's name is considered to be valid if and only if all the following conditions
    are met:
    - There should not be more than three digits ('0'-'9') in the file's name.
    - The file's name contains exactly one dot '.'
    - The substring before the dot should not be empty, and it starts with a letter from
    the latin alphapet ('a'-'z' and 'A'-'Z').
    - The substring after the dot should be one of these: ['txt', 'exe', 'dll']
test_cases:
  - input: "example.txt"
    expected_output: "Yes"
  - input: "1example.dll"
    expected_output: "No"
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (file_name : String) : String :=
  let digit_count := (file_name.data.filter Char.isDigit).length
  let dot_count := (file_name.data.filter (· = '.')).length
  if digit_count > 3 then "No"
  else if dot_count ≠ 1 then "No"
  else 
    let parts := file_name.split (· = '.')
    if parts.length ≠ 2 then "No"
    else
      let before := parts[0]!
      let after := parts[1]!
      if before = "" then "No"
      else if ¬(before.get! 0).isAlpha then "No"  
      else if after = "txt" ∨ after = "exe" ∨ after = "dll" then "Yes"
      else "No"

def problem_spec
-- function signature
(impl: String → String)
-- inputs
(file_name : String) :=
-- spec
let spec (result: String) :=
let valid := (file_name.data.filter Char.isDigit).length ≤ 3 ∧
  (file_name.data.filter (· = '.')).length = 1 ∧
  ∃ before after : String,
    file_name = before ++ "." ++ after ∧
    before ≠ "" ∧
    Char.isAlpha (before.get! 0) ∧
    (after = "txt" ∨ after = "exe" ∨ after = "dll")
(result = "Yes" ↔ valid) ∧
(result = "No" ↔ ¬valid)

-- program termination
∃ result, impl file_name = result ∧
-- return value satisfies spec
spec result

theorem correctness
(file_name : String)
: problem_spec implementation file_name := by
  simp [problem_spec]
  use implementation file_name
  constructor
  · rfl
  · simp [implementation]
    by_cases h_digit : (file_name.data.filter Char.isDigit).length > 3
    · simp [h_digit]
      constructor
      · intro h
        contradiction
      · intro h
        have : (file_name.data.filter Char.isDigit).length ≤ 3 := by
          obtain ⟨_, ⟨_, _⟩, _⟩ := h
          assumption
        omega
    · simp [h_digit]
      by_cases h_dot : (file_name.data.filter (· = '.')).length ≠ 1
      · simp [h_dot]
        constructor
        · intro h
          contradiction
        · intro h
          have : (file_name.data.filter (· = '.')).length = 1 := by
            obtain ⟨_, ⟨h_dot_eq, _⟩, _⟩ := h
            exact h_dot_eq
          contradiction
      · simp [h_dot]
        by_cases h_parts : (file_name.split (· = '.')).length ≠ 2
        · simp [h_parts]
          constructor
          · intro h
            contradiction
          · intro h
            have h_dot_eq : (file_name.data.filter (· = '.')).length = 1 := by
              obtain ⟨_, ⟨h_eq, _⟩, _⟩ := h
              exact h_eq
            have : ¬(file_name.data.filter (· = '.')).length ≠ 1 := by simp [h_dot_eq]
            contradiction
        · simp [h_parts]
          let parts := file_name.split (· = '.')
          let before := parts[0]!
          let after := parts[1]!
          by_cases h_empty : before = ""
          · simp [h_empty]
            constructor
            · intro h
              contradiction
            · intro h
              obtain ⟨_, _, b, a, h_eq, h_ne, _, _⟩ := h
              have : b ≠ "" := h_ne
              have : before = b := by
                have : parts.length = 2 := by omega
                simp [parts, before]
                sorry
              contradiction
          · simp [h_empty]
            by_cases h_alpha : ¬(before.get! 0).isAlpha
            · simp [h_alpha]
              constructor
              · intro h
                contradiction
              · intro h
                obtain ⟨_, _, b, a, h_eq, h_ne, h_alpha_pos, _⟩ := h
                have : (before.get! 0).isAlpha := by
                  simp [before]
                  sorry
                contradiction
            · simp [h_alpha]
              by_cases h_ext : after = "txt" ∨ after = "exe" ∨ after = "dll"
              · simp [h_ext]
                constructor
                · intro h
                  constructor
                  · omega
                  · constructor
                    · omega
                    · use before, after
                      constructor
                      · sorry -- file_name = before ++ "." ++ after
                      · exact ⟨h_empty, by simp [h_alpha], h_ext⟩
                · intro h
                  rfl
              · simp [h_ext]
                constructor
                · intro h
                  contradiction
                · intro h
                  obtain ⟨_, _, b, a, h_eq, h_ne, h_alpha_pos, h_ext_pos⟩ := h
                  have : after = "txt" ∨ after = "exe" ∨ after = "dll" := by
                    simp [after]
                    sorry
                  contradiction

-- #test implementation "example.txt" = "Yes"
-- #test implementation "1example.dll" = "No"