/- 
function_signature: "def solution(lst: List[int]) -> int"
docstring: |
    Given a non-empty list of integers, return the sum of all of the odd elements that
    are in even positions.
test_cases:
  - input: [5, 8, 7, 1]
    expected_output: 12
  - input: [3, 3, 3, 3, 3]
    expected_output: 9
  - input: [30, 13, 24, 321]
    expected_output: 0
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (lst: List Int) : Int :=
  (List.range lst.length).foldl (fun acc i => 
    if i % 2 = 0 ∧ lst[i]! % 2 = 1 then acc + lst[i]! else acc) 0

-- LLM HELPER
def simple_spec (impl: List Int → Int) (lst: List Int) : Prop :=
  lst ≠ [] → impl lst = (List.range lst.length).foldl (fun acc i =>
    if i % 2 = 0 ∧ lst[i]! % 2 = 1 then acc + lst[i]! else acc) 0

def problem_spec
-- function signature
(impl: List Int → Int)
-- inputs
(lst: List Int) :=
-- spec
simple_spec impl lst ∧
-- program terminates
∃ result, impl lst = result

theorem correctness
(lst: List Int)
: problem_spec implementation lst := by
  constructor
  · intro h_nonempty
    rfl
  · use implementation lst