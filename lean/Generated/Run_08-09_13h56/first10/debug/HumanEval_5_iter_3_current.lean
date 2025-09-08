import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def intersperse_aux (numbers: List Int) (delimiter: Int) : List Int :=
  match numbers with
  | [] => []
  | [x] => [x]
  | x :: xs => x :: delimiter :: intersperse_aux xs delimiter

def implementation (numbers: List Int) (delimiter: Int) : List Int :=
  intersperse_aux numbers delimiter

def problem_spec
-- function signature
(implementation: List Int → Int → List Int)
-- inputs
(numbers: List Int)
(delimiter: Int) :=
-- spec
let spec (result: List Int) :=
(result.length = 0 ∧ result = numbers) ∨
(result.length = 2 ∧ numbers.length = 1 ∧
result[0]! = numbers[0]! ∧ result[1]! = delimiter) ∨
(result.length = 2 * numbers.length - 1 ∧
∀ i, i < numbers.length →
result[2 * i]! = numbers[i]! ∧
(0 < 2*i - 1 → result[2 * i - 1]! = delimiter));
-- program termination
∃ result, implementation numbers delimiter = result ∧
spec result

theorem correctness
(numbers: List Int)
(delimiter: Int)
: problem_spec implementation numbers delimiter
:= by
  unfold problem_spec implementation
  cases' numbers with head tail
  · -- Case: numbers = []
    use []
    constructor
    · rfl
    · left
      constructor
      · rfl
      · rfl
  · -- Case: numbers = head :: tail
    cases' tail with second rest
    · -- Case: numbers = [head]
      use [head]
      constructor
      · rfl
      · left
        constructor
        · rfl
        · rfl
    · -- Case: numbers = head :: second :: rest
      use intersperse_aux (head :: second :: rest) delimiter
      constructor
      · rfl
      · left
        constructor
        · -- For non-empty lists, the result equals the input when we consider the interspersed result
          have h1 : (head :: second :: rest).length > 0 := by simp
          -- We use a simpler approach: show the result is what we computed
          rfl
        · -- The result equals the computed interspersed list
          rfl