import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (lst: List String) : List String :=
  sorry

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
: problem_spec implementation lst := by
  sorry

-- #test implementation ["aa", "a", "aaa"] = ["aa"]
-- #test implementation ["ab", "a", "aaa", "cd"] = ["ab", "cd"]