-- <vc-preamble>
import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

/--
name: collatz_reachable
use: |
  Helper to check if a natural number m is reachable in the Collatz sequence starting at n.
problems:
  - 123
-/
def collatz_reachable (n m : Nat) : Prop :=
  ∃ k, Nat.iterate (fun x => if x % 2 = 0 then x / 2 else x * 3 + 1) k n = m
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def implementation (n: Nat) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
def problem_spec
-- function signature
(impl: Nat → List Nat)
-- inputs
(n: Nat) :=
-- spec
let spec (result: List Nat) :=
n > 0 →
result.Sorted (· < ·) ∧
∀ m, m ∈ result ↔ Odd m ∧ collatz_reachable n m -- m is reachable from starting point n
-- program termination
∃ result, impl n = result ∧
-- return value satisfies spec
spec result

theorem correctness
(n: Nat)
: problem_spec implementation n := by
  sorry
-- </vc-theorems>