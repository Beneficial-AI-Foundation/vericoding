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
  n > 0 →
    (∃ i, Nat.fib i = result ∧ Nat.Prime result ∧
      (∃! S : Finset Nat, S.card = n - 1 ∧
      (∀ y ∈ S, (∃ k, y = Nat.fib k) ∧ y < result ∧ Nat.Prime y))
    )
-- program termination
∃ result, implementation n = result ∧
spec result

theorem correctness
(n: Nat)
: problem_spec implementation n
:= by
  sorry

-- #test implementation 1 = 2
-- #test implementation 2 = 3
-- #test implementation 3 = 5
-- #test implementation 4 = 13
-- #test implementation 5 = 89