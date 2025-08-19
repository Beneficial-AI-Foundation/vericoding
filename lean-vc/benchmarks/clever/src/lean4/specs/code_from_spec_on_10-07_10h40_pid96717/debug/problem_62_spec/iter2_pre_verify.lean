import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

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
def check_derivative : List Int → List Int
| [] => []
| [_] => []
| (a :: b :: rest) => (b - a) :: check_derivative (b :: rest)

def implementation (xs: List Int) : List Int := 
  (check_derivative xs.reverse).reverse

-- LLM HELPER
lemma check_derivative_length : ∀ (xs : List Int), (check_derivative xs).length = xs.length - 1
| [] => by simp [check_derivative]
| [_] => by simp [check_derivative]
| (a :: b :: rest) => by
  simp [check_derivative]
  rw [check_derivative_length (b :: rest)]
  simp [List.length]
  cases rest with
  | nil => simp
  | cons _ _ => simp; rfl

-- LLM HELPER
lemma reverse_length : ∀ (xs : List Int), xs.reverse.length = xs.length
| [] => by simp
| (a :: rest) => by
  simp [List.reverse_cons, List.length_append]
  rw [reverse_length rest]

theorem correctness
(xs: List Int)
: problem_spec implementation xs := by
  unfold problem_spec implementation
  use (check_derivative xs.reverse).reverse
  constructor
  · rfl
  · constructor
    · rw [List.length_reverse, check_derivative_length, reverse_length]
    · rfl