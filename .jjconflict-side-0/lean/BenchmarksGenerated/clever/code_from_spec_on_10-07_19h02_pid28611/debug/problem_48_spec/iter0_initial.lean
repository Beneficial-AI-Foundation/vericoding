import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

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

-- LLM HELPER
def is_palindrome (s : String) : Bool :=
  s.data = s.data.reverse

def implementation (string: String) : Bool := is_palindrome string

-- LLM HELPER
lemma implementation_correct (s : String) : implementation s ↔ is_palindrome s := by
  simp [implementation]

theorem correctness
(s: String)
: problem_spec implementation s
:= by
  simp [problem_spec]
  use implementation s
  constructor
  · rfl
  · exact implementation_correct s