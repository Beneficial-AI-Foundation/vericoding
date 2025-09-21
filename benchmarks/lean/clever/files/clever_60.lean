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
(n : Nat) :=
-- spec
let spec (result: Nat) :=
  0 < n →
  (result = 1 ↔ n = 1) ∧
  (∀ i, implementation (i + 1) - (implementation i) = i + 1)
-- program termination
∃ result, implementation n = result ∧
spec result

theorem correctness
(n: Nat)
: problem_spec implementation n
:= by
  sorry
-- </vc-theorems>