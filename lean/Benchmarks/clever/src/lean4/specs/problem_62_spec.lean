import Benchmarks.Clever.CommonDefs
import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Basic

/-- Check derivative of a list -/
def check_derivative (xs : List Int) : List Int := sorry

def problem_spec
-- function signature
(impl: List Int → List Int)
-- inputs
(xs: List Int) :=
-- spec
let spec (result: List Int) :=
  result.length = xs.length - 1 ∧
  result = (check_derivative xs.reverse).reverse
-- program terminates
∃ result, impl xs = result ∧
-- return value satisfies spec
spec result

def implementation (xs: List Int) : List Int := sorry

theorem correctness
(xs: List Int)
: problem_spec implementation xs := sorry
