import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: String → List String)
-- inputs
(string: String) :=
-- spec
let spec (result: List String) :=
result.length = string.length ∧
∀ i, i < result.length →
result[i]! = string.take (i + 1);
-- program termination
∃ result, implementation string = result ∧
spec result

def implementation (string: String) : List String := sorry

theorem correctness
(string: String)
: problem_spec implementation string
:= sorry
