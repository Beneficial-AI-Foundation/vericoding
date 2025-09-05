/- 
function_signature: "def digits(n: int) -> int"
docstring: |
    Given a positive integer n, return the product of the odd digits.
    Return 0 if all digits are even.
test_cases:
  - input: 1
    expected_output: 1
  - input: 4
    expected_output: 0
  - input: 235
    expected_output: 15
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (n: Nat) : Nat :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(impl: Nat → Nat)
-- inputs
(n: Nat) :=
-- spec
let spec (result: Nat) :=
  0 < n →
  (n < 10 → (n % 2 = 1 → result = n) ∧ (n % 2 = 0 → result = 0)) ∧
  (10 ≤ n →
    let digit := n % 10;
    let rest := n / 10;
    (digit % 2 = 1 →
      if (Nat.toDigits 10 rest).all (fun x => Even (x.toNat - '0'.toNat))
        then impl rest = 0 ∧ result = digit
      else
        result = impl rest * digit)
    ∧
    (digit % 2 = 0 →
      result = impl rest))
-- program termination
∃ result, impl n = result ∧
-- return value satisfies spec
spec result

theorem correctness
(n: Nat)
: problem_spec implementation n :=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation 1 = 1
-- #test implementation 4 = 0
-- #test implementation 235 = 15