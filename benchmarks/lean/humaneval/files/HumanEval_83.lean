/- 
function_signature: "def starts_one_ends(n: int) -> int"
docstring: |
    Given a positive integer n, return the count of the numbers of n-digit
    positive integers that start or end with 1.
    Note: For reviewer, I believe this is the most straightforward spec, and I am relying on Set cardianlity not being computable in general. The point of this problem is really to privide a formula.
    Note: But I guess a program that goes through each number and adds 1 will be the same as a program that computes in O(1) under this view.
test_cases:
  - input: 1
    output: 1
  - input: 2
    output: 18
-/

import Imports.AllImports

-- <vc-helpers>
-- </vc-helpers>

def implementation (n: Nat) : Nat :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(implementation: Nat → Nat)
-- inputs
(n: Nat) :=
-- spec
let spec (result : Nat) :=
  0 < n →
  result = {k : ℕ | 10 ^ (n - 1) ≤ k ∧ k < 10 ^ n ∧ (k.repr.front = '1' ∨ k.repr.back = '1')}.ncard
-- program termination
∃ result,
  implementation n = result ∧
  spec result

theorem correctness
(n: Nat)
: problem_spec implementation n
:=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation 1 = 1
-- #test implementation 2 = 18