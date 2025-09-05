/- 
function_signature: "def sorted_list_sum(lst: List[str]) -> List[str]"
docstring: |
    Write a function that accepts a list of strings as a parameter,
    deletes the strings that have odd lengths from it,
    and returns the resulted list with a sorted order,
    The list is always a list of strings and never an array of numbers,
    and it may contain duplicates.
    The order of the list should be ascending by length of each word, and you
    should return the list sorted by that rule.
    If two words have the same length, sort the list alphabetically.
    The function should return a list of strings in sorted order.
    You may assume that all words will have the same length.
test_cases:
  - input: ["aa", "a", "aaa"]
    output: ["aa"]
  - input: ["ab", "a", "aaa", "cd"]
    output: ["ab", "cd"]
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (lst: List String) : List String :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(impl: List String → List String)
-- inputs
(lst: List String) :=
-- spec
let spec (result: List String) :=
match result with
| [] => ∀ str ∈ lst, Odd str.length
| head::tail =>
  Even head.length ∧
  (∀ str ∈ lst,
    Odd str.length ∨
    str.length > head.length ∨
    str.length = head.length ∧ str ≥ head)
  ∧ impl (lst.erase head) = tail
-- program termination
∃ result, impl lst = result ∧
-- return value satisfies spec
spec result

theorem correctness
(lst: List String)
: problem_spec implementation lst :=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation ["aa", "a", "aaa"] = ["aa"]
-- #test implementation ["ab", "a", "aaa", "cd"] = ["ab", "cd"]