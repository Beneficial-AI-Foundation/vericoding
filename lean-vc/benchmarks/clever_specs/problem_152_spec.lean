import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(impl: List Rat → List Rat → List Rat)
-- inputs
(scores guesses: List Rat) :=
-- spec
let spec (result: List Rat) :=
  result.length = scores.length ∧
  scores.length = guesses.length ∧
  ∀ i, i < scores.length →
  if scores[i]! > guesses[i]! then result[i]! + guesses[i]! = scores[i]!
  else result[i]! + scores[i]! = guesses[i]!
-- program terminates
∃ result, impl scores guesses = result ∧
-- return value satisfies spec
spec result

def implementation (scores guesses: List Rat) : List Rat := sorry

theorem correctness
(scores guesses: List Rat)
: problem_spec implementation scores guesses := sorry
