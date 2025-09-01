/- 
function_signature: "def is_sorted(lst: List[int]) -> Bool"
docstring: |
    Given a list of numbers, return whether or not they are sorted
    in ascending order. If list has more than 1 duplicate of the same
    number, return False. Assume no negative numbers and only integers.
test_cases:
  - input: [5]
    expected_output: True
  - input: [1, 2, 3, 4, 5]
    expected_output: True
  - input: [1, 3, 2, 4, 5]
    expected_output: False
  - input: [1, 2, 3, 4, 5, 6]
    expected_outupt: True
  - input: [1, 2, 3, 4, 5, 6, 7]
    expected_output: True
  - input: [1, 3, 2, 4, 5, 6, 7]
    expected_output: False
  - input: [1, 2, 2, 3, 3, 4]
    expected_output: True
  - input: [1, 2, 2, 2, 3, 4]
    expected_output: False
-/

import Imports.AllImports

-- <vc-helpers>
-- </vc-helpers>

def implementation (lst: List Int) : Bool :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(impl: List Int → Bool)
-- inputs
(lst: List Int) :=
-- spec
let sorted_ascending := lst.Sorted (· ≤ ·);
let ms := Multiset.ofList lst;
let multiple_duplicates := ∃ i, i ∈ lst ∧ 2 < ms.count i;
let spec (res: Bool) :=
  res → sorted_ascending ∧
  res → ¬multiple_duplicates ∧
  multiple_duplicates → ¬res ∧
  ¬sorted_ascending → ¬res;
-- program terminates
∃ result, impl lst = result ∧
-- return value satisfies spec
spec result

theorem correctness
(lst: List Int)
: problem_spec implementation lst :=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation [5] = true
-- #test implementation [1, 2, 3, 4, 5] = true
-- #test implementation [1, 3, 2, 4, 5] = false
-- #test implementation [1, 2, 3, 4, 5, 6] = true
-- #test implementation [1, 2, 3, 4, 5, 6, 7] = true
-- #test implementation [1, 3, 2, 4, 5, 6, 7] = false
-- #test implementation [1, 2, 2, 3, 3, 4] = true
-- #test implementation [1, 2, 2, 2, 3, 4] = false