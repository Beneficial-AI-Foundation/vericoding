import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

def problem_spec
-- function signature
(implementation: Nat → Nat)
-- inputs
(n: Nat) :=
-- spec
let spec (result: Nat) :=
  1 < n ∧ ¬ Nat.Prime n →
  (Nat.Prime result ∧ result ∣ n ∧
  ∀ i, i < n ∧ i ∣ n ∧ Nat.Prime i → i ≤ result);
-- program termination
∃ result, implementation n = result ∧
spec result

-- <vc-helpers>

-- </vc-helpers>

-- <vc-description>
/-
function_signature: "def largest_prime_factor(n: Nat) -> Nat"
docstring: |
    Return the largest prime factor of n. Assume n > 1 and is not a prime.
test_cases:
  - input: 13195
    expected_output: 29
  - input: 2048
    expected_output: 2
-/
-- </vc-description>

-- <vc-spec>
def implementation (n: Nat) : Nat :=
-- </vc-spec>
-- <vc-code>
sorry
-- </vc-code>

-- <vc-theorem>
theorem correctness
(n: Nat)
: problem_spec implementation n
:=
-- </vc-theorem>
-- <vc-proof>
by
  sorry
-- </vc-proof>

-- #test implementation 13195 = 29
-- #test implementation 2048 = 2