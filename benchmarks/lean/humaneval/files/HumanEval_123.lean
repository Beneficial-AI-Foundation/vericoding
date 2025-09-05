/- 
function_signature: "def get_odd_collatz (n: int) -> List[int]"
docstring: |
    Given a positive integer n, return a sorted list that has the odd numbers in collatz sequence.

    The Collatz conjecture is a conjecture in mathematics that concerns a sequence defined
    as follows: start with any positive integer n. Then each term is obtained from the
    previous term as follows: if the previous term is even, the next term is one half of
    the previous term. If the previous term is odd, the next term is 3 times the previous
    term plus 1. The conjecture is that no matter what value of n, the sequence will always reach 1.

    Note:
        1. Collatz(1) is [1].
        2. returned list sorted in increasing order.
test_cases:
  - input: 5
    expected_output: [1, 5]
-/

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

-- <vc-helpers>
-- </vc-helpers>

def implementation (n: Nat) : List Nat :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

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
: problem_spec implementation n :=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation 5 = [1, 5]