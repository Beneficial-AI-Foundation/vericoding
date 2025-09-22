-- <vc-preamble>
import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def implementation (n: Nat) : List Int:=
  sorry
-- </vc-definitions>

-- <vc-theorems>
def problem_spec
-- function signature
(impl: Nat → List Int)
-- inputs
(n: Nat) :=
-- spec
let spec (result: List Int) :=
  0 < result.length ∧
  result.length = n ∧
  let i := result.length-1;
  (i = 0 → result[0]! = 1) ∧ -- base case
  (i = 1 → result[1]! = 3) ∧
  (2 ≤ i ∧ i % 2 = 0 → result[i]! = 1 + i / 2) ∧
  (2 ≤ i ∧ i % 2 = 1 → result[i]! = result[i-2]! + result[i-1]! + (1 + (i+1) / 2)) ∧
  if i = 0 then true else result.take i = impl (i-1)
-- program termination
∃ result, impl n = result ∧
-- return value satisfies spec
spec result

theorem correctness
(n: Nat)
: problem_spec implementation n := by
  sorry
-- </vc-theorems>