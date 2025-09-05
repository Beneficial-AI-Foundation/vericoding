/- 
function_signature: "def next_smallest(lst: List[int]) -> Optional[int]"
docstring: |
    You are given a list of integers.
    Write a function next_smallest() that returns the 2nd smallest element of the list.
    Return None if there is no such element.
    TODO(George): Remove this when being reviewed
    The spec is defined as: if result is none there is no second smallest element, which
    exists in a finite list iff there are at least two distinct elements in the list.
    If result is some x, then x is the second smallest element of the list, the spec
    obtains the sublist of elements smaller than the result, and checks that this
    sublist does not contain two distinct elements (they are all the same).
test_cases:
  - input: [1, 2, 3, 4, 5]
    output: 2
  - input: [5, 1, 4, 3, 2]
    output: 2
  - input: []
    output: None
  - input: [1, 1]
    output: None
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (lst: List Int) : Option Int :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(implementation: List Int → Option Int)
-- inputs
(lst: List Int) :=
-- spec
let spec (result : Option Int) :=
  match result with
  | none => ¬ (∃ i j, i < lst.length ∧ j < lst.length ∧ i ≠ j ∧ lst[i]! < lst[j]!)
  | some result =>
    let smaller_els := lst.filter (· < result);
    0 < smaller_els.length ∧
    smaller_els.all (λ x => x = smaller_els[0]!);
-- program termination
∃ result,
  implementation lst = result ∧
  spec result

theorem correctness
(lst: List Int)
: problem_spec implementation lst
:=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation [1, 2, 3, 4, 5] = some 2
-- #test implementation [5, 1, 4, 3, 2] = some 2
-- #test implementation [] = none
-- #test implementation [1, 1] = none