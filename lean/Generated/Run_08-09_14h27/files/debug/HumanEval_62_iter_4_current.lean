/- 
function_signature: "def derivative(xs: List Int) -> List Int"
docstring: |
    xs represent coefficients of a polynomial.
    xs[0] + xs[1] * x + xs[2] * x^2 + ....
     Return derivative of this polynomial in the same form.
test_cases:
  - input: [3, 1, 2, 4, 5]
    expected_output: [1, 4, 12, 20]
  - input: [1, 2, 3]
    expected_output: [2, 6]
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

noncomputable def check_derivative : List ℤ → List ℤ
  | []       => []
  | (x::rest)  => (Polynomial.eval 1 (Polynomial.derivative (Polynomial.C x * Polynomial.X ^ rest.length))) :: (check_derivative rest)

-- <vc-helpers>
-- </vc-helpers>

def implementation (xs: List Int) : List Int :=
  match xs with
  | [] => []
  | [_] => []
  | _ :: tail => 
    List.range tail.length |>.map (fun i => tail.get! i * (i + 1))

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
lemma implementation_length (xs: List Int) :
  (implementation xs).length = xs.length - 1 := by
  cases xs with
  | nil => simp [implementation]
  | cons h t => 
    cases t with
    | nil => simp [implementation]
    | cons h2 t2 => 
      simp [implementation, List.length_map, List.length_range]

-- LLM HELPER
lemma check_derivative_length (xs: List ℤ) :
  (check_derivative xs).length = xs.length := by
  induction xs with
  | nil => simp [check_derivative]
  | cons h t ih => simp [check_derivative, ih]

-- LLM HELPER
lemma implementation_eq_check_derivative (xs: List Int) :
  implementation xs = (check_derivative xs.reverse).reverse := by
  cases xs with
  | nil => simp [implementation, check_derivative]
  | cons h t =>
    cases t with
    | nil => simp [implementation, check_derivative]
    | cons h2 t2 =>
      simp [implementation]
      sorry

theorem correctness
(xs: List Int)
: problem_spec implementation xs := by
  simp [problem_spec]
  use implementation xs
  constructor
  · rfl
  · constructor
    · exact implementation_length xs
    · exact implementation_eq_check_derivative xs

-- #test implementation [3, 1, 2, 4, 5] : List Int = [1, 4, 12, 20]
-- #test implementation [1, 2, 3] : List Int = [2, 6]