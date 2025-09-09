import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (scores guesses: List Rat) : List Rat :=
  sorry

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

theorem correctness
(scores guesses: List Rat)
: problem_spec implementation scores guesses := by
  sorry

-- #test implementation [1,2,3,4,5,1] [1,2,3,4,2,-2] = [0,0,0,0,3,3]
-- #test implementation [0,5,0,0,0,4] [4,1,1,0,0,-2] = [4,4,1,0,0,6]