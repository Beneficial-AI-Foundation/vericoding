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
  · unfold implementation
    split_ifs with h1 h2 h3 h4 h5 h6
    all_goals simp
    · -- digit_count > 3, returns "No"
      constructor
      · intro h; contradiction
      · intro valid_cond
        obtain ⟨h_digit, _, _⟩ := valid_cond
        omega
    · -- dot_count ≠ 1, returns "No"  
      constructor
      · intro h; contradiction
      · intro valid_cond
        obtain ⟨_, h_dot, _⟩ := valid_cond
        contradiction
    · -- parts.length ≠ 2, returns "No"
      constructor
      · intro h; contradiction  
      · intro valid_cond
        obtain ⟨h_digit, h_dot, before, after, h_eq, h_ne, h_alpha, h_ext⟩ := valid_cond
        -- This case should be impossible when dot_count = 1
        simp at h2
        exfalso
        -- If there's exactly one dot and the string has the right structure,
        -- split should give exactly 2 parts
        have parts_len : (file_name.split (· = '.')).length = 2 := by
          sorry -- This would require proving the relationship between split and dot count
        exact h3 parts_len
    · -- before = "", returns "No"
      constructor
      · intro h; contradiction
      · intro valid_cond
        obtain ⟨_, _, before, after, h_eq, h_ne, _, _⟩ := valid_cond
        -- Need to show parts[0]! = before, which contradicts h_ne
        exfalso
        sorry
    · -- ¬(before.get! 0).isAlpha, returns "No"  
      constructor
      · intro h; contradiction
      · intro valid_cond
        obtain ⟨_, _, before, after, h_eq, h_ne, h_alpha, _⟩ := valid_cond
        -- Need to show parts[0]! = before and contradiction with h_alpha
        exfalso
        sorry
    · -- after not in extensions, returns "No"
      constructor  
      · intro h; contradiction
      · intro valid_cond
        obtain ⟨_, _, before, after, h_eq, h_ne, h_alpha, h_ext⟩ := valid_cond
        -- Need to show parts[1]! = after and contradiction with h_ext
        exfalso
        sorry
    · -- All conditions met, returns "Yes"
      constructor
      · intro h
        constructor
        · -- digit count ≤ 3
          omega
        · constructor
          · -- dot count = 1
            omega  
          · -- exists before after with properties
            use (file_name.split (· = '.'))[0]!, (file_name.split (· = '.'))[1]!
            constructor
            · -- file_name = before ++ "." ++ after
              sorry -- Need to prove split property
            · exact ⟨h4, by simp at h5; exact h5, h6⟩
      · intro valid_cond
        rfl

-- #test implementation "example.txt" = "Yes"
-- #test implementation "1example.dll" = "No"