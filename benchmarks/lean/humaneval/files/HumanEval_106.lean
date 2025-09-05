/- 
function_signature: "def f(n: int) -> List[int]"
docstring: |
    Implement the function f that takes n as a parameter,
    and returns a list of size n, such that the value of the element at index i is the factorial of i if i is even
    or the sum of numbers from 1 to i otherwise.
    i starts from 1.
    the factorial of i is the multiplication of the numbers from 1 to i (1 * 2 * ... * i).
test_cases:
  - input: 5
    expected_output: [1, 2, 6, 24, 15]
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (n: Int) : List Int :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(implementation: Int → List Int)
-- inputs
(n: Int) :=
-- spec
let spec (result: List Int) :=
  (result.length = n) ∧
  (forall i: Nat, (1 ≤ i ∧ i ≤ n ∧ Even i) → (result[i-1]! = Nat.factorial i)) ∧
  (forall i: Nat, (1 ≤ i ∧ i ≤ n ∧ Odd i) → (result[i-1]! = (List.range (i+1)).sum))
-- program termination
∃ result, implementation n = result ∧
spec result

theorem correctness
(n: Int)
: problem_spec implementation n
:=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation 5 = [1, 2, 6, 24, 15]
-- #test implementation 7 = [1, 2, 6, 24, 15, 720, 28]
-- #test implementation 1 = [1]
-- #test implementation 3 = [1, 2, 6]