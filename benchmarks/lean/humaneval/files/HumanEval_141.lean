import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (file_name : String) : String :=
  sorry

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

theorem correctness
(file_name : String)
: problem_spec implementation file_name := by
  sorry

-- #test implementation "example.txt" = "Yes"
-- #test implementation "1example.dll" = "No"