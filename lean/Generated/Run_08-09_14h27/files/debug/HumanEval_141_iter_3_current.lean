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
  · constructor
    · intro h
      simp [h]
      have : implementation file_name = "Yes" := h
      simp [implementation] at this
      split_ifs at this with h1 h2 h3 h4 h5 h6 <;> simp at this
      constructor
      · omega
      · constructor
        · exact Nat.eq_of_le_of_lt_succ (Nat.not_lt.mp h2) (Nat.lt_one_iff.mp (Nat.not_lt.mp h2))
        · let parts := file_name.split (· = '.')
          let before := parts[0]!
          let after := parts[1]!
          use before, after
          constructor
          · have : parts.length = 2 := Nat.eq_of_le_of_lt_succ (Nat.not_lt.mp h3) (Nat.lt_succ_iff.mp (Nat.not_lt.mp h3))
            rw [String.split_eq_cons_split]
            sorry -- reconstruction property
          · constructor
            · exact Ne.symm (ne_of_beq_false h4)
            · constructor
              · exact Bool.eq_true_of_ne_false h5
              · exact h6
    · intro h
      simp [h]
      obtain ⟨h_digit, h_dot, before, after, h_eq, h_ne, h_alpha, h_ext⟩ := h
      simp [implementation]
      have h1 : ¬((file_name.data.filter Char.isDigit).length > 3) := by omega
      have h2 : ¬((file_name.data.filter (· = '.')).length ≠ 1) := by simp [h_dot]
      simp [h1, h2]
      have h3 : ¬((file_name.split (· = '.')).length ≠ 2) := by
        rw [h_eq]
        simp [String.split]
        sorry -- split property
      simp [h3]
      rw [h_eq]
      simp [String.split]
      have h4 : ¬(before = "") := h_ne
      have h5 : ¬¬((before.get! 0).isAlpha) := by simp [h_alpha]
      simp [h4, h5, h_ext]

-- #test implementation "example.txt" = "Yes"
-- #test implementation "1example.dll" = "No"