import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (n: Nat) : Nat :=
  sorry

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

theorem correctness
(n: Nat)
: problem_spec implementation n
:= by
  sorry

-- #test implementation 13195 = 29
-- #test implementation 2048 = 2