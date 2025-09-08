/- 
function_signature: "def total_match(lst1: List[str], lst2: List[str]) -> List[str]"
docstring: |
  Write a function that accepts two lists of strings and returns the list that has
  total number of chars in the all strings of the list less than the other list.
  If the two lists have the same number of chars, return the first list.
test_cases:
  - input: ([], [])
    expected_output: []
  - input: (['hi', 'admin'], ['hI', 'Hi'])
    expected_output: ['hI', 'Hi']
  - input: (['hi', 'admin'], ['hi', 'hi', 'admin', 'project'])
    expected_output: ['hi', 'admin']
  - input: (['hi', 'admin'], ['hI', 'hi', 'hi'])
    expected_output: ['hI', 'hi', 'hi']
  - input: (['4'], ['1', '2', '3', '4', '5'])
    expected_output: ['4']
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def sum_chars (xs: List String) : Int :=
  xs.foldl (λ acc a => acc + a.length) 0

def implementation (lst1: List String) (lst2: List String) : List String :=
  if sum_chars lst1 ≤ sum_chars lst2 then lst1 else lst2

def problem_spec
-- function signature
(implementation: List String → List String → List String)
-- inputs
(lst1: List String) (lst2: List String) :=
let sum_chars (xs: List String) : Int :=
  xs.foldl (λ acc a => acc + a.length) 0;
-- spec
let spec (result : List String) :=
  ((result = lst1) ∨ (result = lst2))
  ∧
  (sum_chars result ≤ sum_chars lst1)
  ∧
  (sum_chars result ≤ sum_chars lst2)
  ∧
  ((sum_chars lst1 = sum_chars lst2) → (result = lst1))
-- program termination
∃ result, implementation lst1 lst2 = result ∧
spec result

theorem correctness
(lst1: List String) (lst2: List String)
: problem_spec implementation lst1 lst2
:= by
  unfold problem_spec
  unfold implementation
  split_ifs with h
  · -- Case: sum_chars lst1 ≤ sum_chars lst2
    use lst1
    constructor
    · simp
    · constructor
      · left
        rfl
      · constructor
        · simp
        · constructor
          · exact h
          · intro h_eq
            rfl
  · -- Case: ¬(sum_chars lst1 ≤ sum_chars lst2)
    use lst2
    constructor
    · simp
    · constructor
      · right
        rfl
      · constructor
        · push_neg at h
          exact Int.le_of_lt h
        · constructor
          · simp
          · intro h_eq
            exfalso
            have : sum_chars lst1 = sum_chars lst2 := h_eq
            have : sum_chars lst1 ≤ sum_chars lst2 := Int.le_of_eq this
            exact h this

-- #test implementation [] [] = []
-- #test implementation ["hi", "admin"] ["hi", "hi"] = ["hi", "hi"]
-- #test implementation ["hi", "admin"] ["hi", "hi", "admin", "project"] = ["hi", "admin"]
-- #test implementation ["4"] ["1", "2", "3", "4", "5"] = ["4"]
-- #test implementation ["hi", "admin"] ["hI", "Hi"] = ["hI", "Hi"]
-- #test implementation ["hi", "admin"] ["hI", "hi", "hi"] = ["hI", "hi", "hi"]
-- #test implementation ["hi", "admin"] ["hI", "hi", "hii"] = ["hi", "admin"]
-- #test implementation [] ["this"] = []
-- #test implementation ["this"] [] == []