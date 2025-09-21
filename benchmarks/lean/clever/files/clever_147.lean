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
(impl: Nat → Nat)
-- inputs
(n: Nat) :=
-- spec
let spec (result: Nat) :=
∃ (S : Finset (Nat × Nat × Nat)), S.card = result ∧
  ∀ (triple: Nat × Nat × Nat),
    let (i, j, k) := triple;
    let a_i := i * i - i + 1;
    let a_j := j * j - j + 1;
    let a_k := k * k - k + 1;
    (1 ≤ i ∧ i < j ∧ j < k ∧ k ≤ n ∧
    (a_i + a_j + a_k) % 3 = 0)
    ↔ triple ∈ S
-- program termination
∃ result, impl n = result ∧
-- return value satisfies spec
spec result

theorem correctness
(n: Nat)
: problem_spec implementation n := by
  sorry
-- </vc-theorems>