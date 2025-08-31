/- 
function_signature: "def largest_smallest_integers(lst: List[int]) -> Tuple[ Optional[Int], Optional[Int] ]"
docstring: |
    Create a function that returns a tuple (a, b), where 'a' is
    the largest of negative integers, and 'b' is the smallest
    of positive integers in a list.
    If there is no negative or positive integers, return them as None.
test_cases:
  - input: [2, 4, 1, 3, 5, 7]
    expected_output: (None, 1)
  - input: []
    expected_output: (None, None)
  - input: [0]
    expected_output: (None, None)
-/

import Imports.AllImports

-- <vc-helpers>
-- </vc-helpers>

def implementation (lst: List Int) : (Option Int × Option Int) :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(impl: List Int → Option Int × Option Int)
-- inputs
(lst: List Int) :=
-- spec
let spec (result: Option Int × Option Int) :=
  let (a, b) := result;
  (match a with
  | none => ¬(∃ i, i ∈ lst ∧ i < 0)
  | some a => a < 0 ∧ a ∈ lst ∧ ∀ i, i ∈ lst ∧ i < 0 → i ≤ a) ∧
  (match b with
  | none => ¬(∃ i, i ∈ lst ∧ 0 < i)
  | some b => 0 < b ∧ b ∈ lst ∧ ∀ i, i ∈ lst ∧ 0 < i → b ≤ i)
-- program termination
∃ result, impl lst = result ∧
-- return value satisfies spec
spec result

theorem correctness
(lst: List Int)
: problem_spec implementation lst :=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation [2, 4, 1, 3, 5, 7] = (none, some 1)
-- #test implementation [] = (none, none)
-- #test implementation [0] = (none, none)