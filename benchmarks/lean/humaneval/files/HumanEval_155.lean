/- 
function_signature: "def even_odd_count(num: int) -> Tuple[int, int]"
docstring: |
    Given an integer. return a tuple that has the number of even and odd digits respectively.
test_cases:
  - input: -12
    expected_output: [1, 1]
  - input: 123
    expected_output: [1, 2]
-/

import Imports.AllImports

-- <vc-helpers>
-- </vc-helpers>

def implementation (num: Int) : Int × Int :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(impl: Int → Int × Int)
-- inputs
(num: Int) :=
-- spec
let spec (result: Int × Int) :=
  let (even_count, odd_count) := result;
  let numAbs := |num|.toNat;
  let numBy10 := numAbs/10;
  let (even_count', odd_count') := impl numBy10;
  (result = impl numAbs) ∧
  (0 ≤ num → (Even num ↔ 1 + even_count' = even_count) ∧ (Odd num ↔ even_count' = even_count)) ∧
  (0 ≤ num → (Odd num ↔ 1 + odd_count' = odd_count) ∧ (Even num ↔ odd_count' = odd_count));
-- program terminates
∃ result, impl num = result ∧
-- return value satisfies spec
spec result

theorem correctness
(num: Int)
: problem_spec implementation num :=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation -12 = (1, 1)
-- #test implementation 123 = (1, 2)