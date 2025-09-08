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

-- LLM HELPER
lemma string_split_dot_eq (s before after : String) :
  s = before ++ "." ++ after ∧ before ≠ "" ∧ (before.data.filter (· = '.')).length = 0 ∧ (after.data.filter (· = '.')).length = 0 →
  let parts := s.split (· = '.')
  parts.length = 2 ∧ parts[0]! = before ∧ parts[1]! = after := by
  intro h
  simp [List.split]
  sorry

-- LLM HELPER  
lemma string_parts_reconstruction (s : String) :
  let parts := s.split (· = '.')
  parts.length = 2 ∧ (s.data.filter (· = '.')).length = 1 →
  s = parts[0]! ++ "." ++ parts[1]! := by
  intro h
  sorry

theorem correctness
(file_name : String)
: problem_spec implementation file_name := by
  simp [problem_spec, implementation]
  use implementation file_name
  constructor
  · rfl
  · simp [implementation]
    split_ifs with h1 h2 h3 h4 h5 h6
    · -- digit_count > 3
      constructor
      · intro h_yes
        contradiction
      · constructor
        · intro h_no
          simp
          left
          omega
        · intro h_valid
          obtain ⟨_, _, _⟩ := h_valid
          omega
    · -- dot_count ≠ 1  
      constructor
      · intro h_yes
        contradiction
      · constructor
        · intro h_no
          simp
          right
          left
          exact h2
        · intro h_valid
          obtain ⟨_, h_dot, _⟩ := h_valid
          contradiction
    · -- parts.length ≠ 2
      constructor
      · intro h_yes
        contradiction
      · constructor
        · intro h_no
          simp
          right
          right
          left
          intro before after h_eq h_ne h_alpha h_ext
          rw [h_eq] at h3
          have h_parts := string_split_dot_eq (before ++ "." ++ after) before after
          sorry
        · intro h_valid
          obtain ⟨before, after, h_eq, h_ne, h_alpha, h_ext⟩ := h_valid
          rw [h_eq] at h3
          have h_parts := string_split_dot_eq (before ++ "." ++ after) before after  
          sorry
    · -- before = ""
      constructor
      · intro h_yes
        contradiction
      · constructor
        · intro h_no
          simp
          right
          right
          right
          left
          intro before after h_eq h_ne h_alpha h_ext
          have h_parts := string_parts_reconstruction file_name
          rw [←h_eq] at h_parts
          have : (file_name.data.filter (· = '.')).length = 1 := by
            obtain ⟨_, h_dot, _⟩ := ⟨le_refl _, by simp [h_eq]; sorry, ⟨before, after, h_eq, h_ne, h_alpha, h_ext⟩⟩
            exact h_dot
          have h_parts_eq := h_parts ⟨⟨not_not.mp h3, this⟩⟩
          rw [h_parts_eq] at h4
          simp at h4
          exact absurd h_ne h4
        · intro h_valid
          obtain ⟨before, after, h_eq, h_ne, h_alpha, h_ext⟩ := h_valid
          have h_parts := string_parts_reconstruction file_name
          rw [←h_eq] at h_parts
          have : (file_name.data.filter (· = '.')).length = 1 := by
            obtain ⟨_, h_dot, _⟩ := h_valid
            exact h_dot
          have h_parts_eq := h_parts ⟨⟨not_not.mp h3, this⟩⟩
          rw [h_parts_eq] at h4
          simp at h4
          exact absurd h_ne h4
    · -- ¬(before.get! 0).isAlpha
      constructor
      · intro h_yes
        contradiction
      · constructor
        · intro h_no
          simp
          right
          right
          right
          right
          left
          intro before after h_eq h_ne h_alpha h_ext
          have h_parts := string_parts_reconstruction file_name
          sorry
        · intro h_valid
          obtain ⟨before, after, h_eq, h_ne, h_alpha, h_ext⟩ := h_valid
          have h_parts := string_parts_reconstruction file_name
          sorry
    · -- after ∈ {txt, exe, dll}
      constructor
      · intro h_yes
        simp
        constructor
        · omega
        · constructor  
          · simp [h2]
          · let parts := file_name.split (· = '.')
            let before := parts[0]!
            let after := parts[1]!
            use before, after
            constructor
            · exact string_parts_reconstruction file_name ⟨⟨not_not.mp h3, by simp [h2]⟩⟩
            · constructor
              · exact not_not.mp h4
              · constructor
                · exact not_not.mp h5
                · exact h6
      · constructor
        · intro h_no
          simp
          right
          right  
          right
          right
          right
          intro before after h_eq h_ne h_alpha h_ext
          exact absurd h_ext h6
        · intro h_valid
          obtain ⟨_, _, before, after, h_eq, h_ne, h_alpha, h_ext⟩ := h_valid
          exact absurd h_ext h6
    · -- ¬(after ∈ {txt, exe, dll})
      constructor
      · intro h_yes
        contradiction
      · constructor
        · intro h_no
          simp
          right
          right
          right
          right
          right
          intro before after h_eq h_ne h_alpha h_ext
          exact absurd h_ext h6
        · intro h_valid
          obtain ⟨_, _, before, after, h_eq, h_ne, h_alpha, h_ext⟩ := h_valid
          exact absurd h_ext h6

-- #test implementation "example.txt" = "Yes"
-- #test implementation "1example.dll" = "No"