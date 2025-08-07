import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Basic

/-- Check if a string is a palindrome -/
def is_palindrome (s : String) : Bool := sorry

def problem_spec
-- function signature
(implementation: String → Bool)
-- inputs
(string: String) :=
-- spec
let spec (result: Bool) :=
result ↔ is_palindrome string
-- program termination
∃ result, implementation string = result ∧
spec result

def implementation (string: String) : Bool := sorry

theorem correctness
(s: String)
: problem_spec implementation s
:= sorry
