import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def is_palindrome (s : String) : Bool :=
  s.data = s.data.reverse

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

def implementation (string: String) : Bool := 
  string.data = string.data.reverse

-- LLM HELPER
lemma implementation_eq_is_palindrome (s : String) : 
  implementation s = is_palindrome s := by
  rfl

theorem correctness
(s: String)
: problem_spec implementation s
:= by
  unfold problem_spec
  use implementation s
  constructor
  · rfl
  · rw [implementation_eq_is_palindrome]
    rfl