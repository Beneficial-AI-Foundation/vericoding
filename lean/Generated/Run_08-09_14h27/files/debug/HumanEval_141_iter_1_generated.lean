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

-- LLM HELPER
def count_dots (s : String) : Nat :=
  (s.toList.filter (· = '.')).length

-- LLM HELPER
def count_digits (s : String) : Nat :=
  (s.toList.filter Char.isDigit).length

-- LLM HELPER
def split_at_dot (s : String) : Option (String × String) :=
  let parts := s.split (· = '.')
  if parts.length = 2 then
    some (parts[0]!, parts[1]!)
  else
    none

-- LLM HELPER
def is_valid_extension (ext : String) : Bool :=
  ext = "txt" || ext = "exe" || ext = "dll"

-- LLM HELPER
def is_valid_filename (file_name : String) : Bool :=
  count_digits file_name ≤ 3 &&
  count_dots file_name = 1 &&
  match split_at_dot file_name with
  | none => false
  | some (before, after) =>
    before != "" &&
    (before.get? 0).isSome &&
    Char.isAlpha (before.get! 0) &&
    is_valid_extension after

def implementation (file_name : String) : String :=
  if is_valid_filename file_name then "Yes" else "No"

def problem_spec
-- function signature
(impl: String → String)
-- inputs
(file_name : String) :=
-- spec
let spec (result: String) :=
let valid := (file_name.toList.filter Char.isDigit).length ≤ 3 ∧
  (file_name.toList.filter (· = '.')).length = 1 ∧
  ∃ before after : String,
    file_name = before ++ "." ++ after ∧
    before != "" ∧
    Char.isAlpha (before.get! 0) ∧
    (after = "txt" ∨ after = "exe" ∨ after = "dll")
(result = "Yes" ↔ valid) ∧
(result = "No" ↔ ¬valid)

-- program termination
∃ result, impl file_name = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
lemma split_at_dot_correct (s : String) (before after : String) :
  s = before ++ "." ++ after ∧ before != "" ∧ after != "" ∧ count_dots s = 1 →
  split_at_dot s = some (before, after) := by
  intro h
  simp [split_at_dot]
  sorry

-- LLM HELPER
lemma split_at_dot_complete (s : String) (before after : String) :
  split_at_dot s = some (before, after) →
  s = before ++ "." ++ after ∧ before != "" := by
  intro h
  simp [split_at_dot] at h
  sorry

-- LLM HELPER
lemma is_valid_extension_correct (ext : String) :
  is_valid_extension ext = true ↔ (ext = "txt" ∨ ext = "exe" ∨ ext = "dll") := by
  simp [is_valid_extension]
  constructor
  · intro h
    cases' h with h h
    · left; exact h
    · cases' h with h h
      · right; left; exact h
      · right; right; exact h
  · intro h
    cases' h with h h
    · simp [h]
    · cases' h with h h
      · simp [h]
      · simp [h]

theorem correctness
(file_name : String)
: problem_spec implementation file_name := by
  simp [problem_spec, implementation]
  use if is_valid_filename file_name then "Yes" else "No"
  constructor
  · rfl
  · simp
    constructor
    · constructor
      · intro h
        simp [is_valid_filename] at h
        sorry
      · intro h
        simp [is_valid_filename]
        sorry
    · constructor
      · intro h
        simp [is_valid_filename] at h
        sorry  
      · intro h
        simp [is_valid_filename]
        sorry

-- #test implementation "example.txt" = "Yes"
-- #test implementation "1example.dll" = "No"