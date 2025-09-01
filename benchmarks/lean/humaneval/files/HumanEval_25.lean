/- 
function_signature: "def factorize(n: int) -> List[int]"
docstring: |
    Return list of prime factors of given integer in the order from smallest to largest.
    Each of the factors should be listed number of times corresponding to how many times it appeares in factorization.
    Input number should be equal to the product of all factors
test_cases:
  - input: 8
    expected_output: [2, 2, 2]
  - input: 25
    expected_output: [5, 5]
  - input: 70
    expected_output: [2, 5, 7]
-/

import Imports.AllImports

-- <vc-helpers>
-- </vc-helpers>

def implementation (n: Nat) : List Nat :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(implementation: Nat → List Nat)
-- inputs
(n: Nat) :=
-- spec
let spec (result: List Nat) :=
2 ≤ n →
(result.prod = n ∧
List.Sorted Nat.le result ∧
result.all (λ i => n % i = 0 ∧ Nat.Prime i));
-- program termination
∃ result, implementation n = result ∧
spec result

theorem correctness
(n: Nat)
: problem_spec implementation n
:=
-- <vc-proof>
  sorry
-- </vc-proof>

#test implementation 8 = [2, 2, 2]
#test implementation 25 = [5, 5]
#test implementation 70 = [2, 5, 7]