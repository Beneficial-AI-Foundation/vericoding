-- <vc-preamble>
import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def implementation (n: Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
def problem_spec
-- function signature
(implementation: Nat → Nat)
-- inputs
(n: Nat) :=
-- spec
let spec (result: Nat) :=
  (n = 0 → result = 0) ∧
  (0 < n → result = implementation (n - 1) →
    (n % 11 ≠  0 ∧  n % 13 ≠  0) ∨ n.repr.count '7' = 0) ∧
  (0 < n → result ≠ implementation (n - 1) →
    (n % 11 = 0 ∨  n % 13 = 0) ∧
    result - implementation (n - 1) = n.repr.count '7')
-- program termination
∃ result, implementation n = result ∧
spec result

theorem correctness
(n: Nat)
: problem_spec implementation n
:= by
  sorry
-- </vc-theorems>