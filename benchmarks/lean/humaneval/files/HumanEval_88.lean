/- 
function_signature: "def sort_array(lst : list(int)) -> list(int)"
docstring: |
    """
    Given an array of non-negative integers, return a copy of the given array after sorting,
    you will sort the given array in ascending order if the sum( first index value, last index value) is odd,
    or sort it in descending order if the sum( first index value, last index value) is even.
    Note(George): I have elected to ignore the copy part.
test_cases:
  - input: []
    output: []
  - input: [5]
    output: [5]
  - input: [2, 4, 3, 0, 1, 5]
    output: [0, 1, 2, 3, 4, 5]
  - input: [2, 4, 3, 0, 1, 5, 6]
    output: [6, 5, 4, 3, 2, 1, 0]
-/

import Imports.AllImports

-- <vc-helpers>
-- </vc-helpers>

def implementation (lst: List Nat) : List Nat :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(implementation: List Nat → List Nat)
-- inputs
(lst: List Nat) :=
-- spec
let spec (result : List Nat) :=
  lst.length > 0 →
  result.length = lst.length ∧
  (∀ i, i < result.length →
    result[i]! ∈ lst ∧
    lst[i]! ∈ result ∧
    result.count (lst[i]!) = lst.count (lst[i]!)) ∧
  (lst.head! + lst.getLast!) ≡ 1 [MOD 2] →
    result.Sorted Nat.le ∧
  (lst.head! + lst.getLast!) ≡ 0 [MOD 2] →
    result.Sorted (fun a b => a ≥ b)
-- program termination
∃ result,
  implementation lst = result ∧
  spec result

theorem correctness
(lst: List Nat)
: problem_spec implementation lst
:=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation [] = []
-- #test implementation [5] = [5]
-- #test implementation [2, 4, 3, 0, 1, 5] = [0, 1, 2, 3, 4, 5]
-- #test implementation [2, 4, 3, 0, 1, 5, 6] = [6, 5, 4, 3, 2, 1, 0]