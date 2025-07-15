import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def check_derivative : List Int → List Int
| [] => []
| [_] => []
| (x :: y :: rest) => (y - x) :: check_derivative (y :: rest)

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

-- LLM HELPER
lemma check_derivative_length : ∀ xs : List Int, (check_derivative xs).length = xs.length - 1
| [] => by simp [check_derivative]
| [_] => by simp [check_derivative]
| (x :: y :: rest) => by
  simp [check_derivative]
  rw [check_derivative_length (y :: rest)]
  simp [List.length]
  omega

def implementation (xs: List Int) : List Int := (check_derivative xs.reverse).reverse

theorem correctness
(xs: List Int)
: problem_spec implementation xs := by
  unfold problem_spec
  use (check_derivative xs.reverse).reverse
  constructor
  · rfl
  constructor
  · simp [implementation]
    rw [List.length_reverse, check_derivative_length]
    rw [List.length_reverse]
  · rfl