/- 
function_signature: "def median(numbers: List[float]) -> float"
docstring: |
    Return median of elements in the list l
test_cases:
  - input: [3, 1, 2, 4, 5]
    output: 3
  - input: [-10, 4, 6, 1000, 10, 20]
    output: 15.0
-/

import Imports.AllImports

-- <vc-helpers>
-- </vc-helpers>

def implementation (numbers: List Rat) : Rat :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(implementation: List Rat → Rat)
-- inputs
(numbers: List Rat) :=
-- spec
let spec (result: Rat) :=
  0 < numbers.length →
  let less_eq := (numbers.filter (fun x => x ≤ result));
  let more_eq := (numbers.filter (fun x => result ≤ x));
  let max_more_eq := more_eq.max?;
  let min_less_eq := less_eq.min?;
  let less_eq_count := less_eq.length;
  let more_eq_count := more_eq.length;
  let eq_count := (numbers.filter (fun x => x = result)).length;
  (less_eq_count + more_eq_count - eq_count = numbers.length →
  numbers.length ≤ 2 * less_eq_count →
  numbers.length ≤ 2 * more_eq_count) ∧
  ((numbers.length % 2 = 1 →
    result ∈ numbers) ∧
    (numbers.length % 2 = 0 → max_more_eq.isSome ∧
    min_less_eq.isSome ∧
    2 * result = max_more_eq.get! + min_less_eq.get!));
-- program termination
∃ result, implementation numbers = result ∧
spec result

theorem correctness
(numbers: List Rat)
: problem_spec implementation numbers
:=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation [3, 1, 2, 4, 5] = 3
-- #test implementation [-10, 4, 6, 1000, 10, 20] = 15.0