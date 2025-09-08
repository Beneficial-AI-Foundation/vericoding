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

def problem_spec
-- function signature
(impl: List Int → Int)
-- inputs
(lst: List Int) :=
-- spec
let spec (_ : Int) :=
lst ≠ [] → ∀ i,  i < lst.length ∧ i % 2 = 0 →
  (lst.length = 1 → impl lst = 0) ∧
  (i + 1 < lst.length →
    (lst[i + 1]! % 2 = 1 →
    impl (lst.drop i) = lst[i + 1]! + (if i + 2 < lst.length then impl (lst.drop (i+2)) else 0)) ∧
    (lst[i + 1]! % 2 = 0 →
    impl (lst.drop i) = if i + 2 < lst.length then impl (lst.drop (i+2)) else 0)
  )
-- program terminates
∃ result, impl lst = result ∧
-- return value satisfies spec
spec result

theorem correctness
(lst: List Int)
: problem_spec implementation lst := by
  use implementation lst
  constructor
  · rfl
  · intro h_nonempty i h_i
    constructor
    · intro h_len_one
      simp [implementation]
      cases lst with
      | nil => contradiction
      | cons h t =>
        simp at h_len_one
        simp [h_len_one]
        by_cases ho : h % 2 = 1
        · simp [ho]
        · simp [ho]
    · intro h_bound
      constructor
      · intro h_odd
        simp [implementation]
        sorry
      · intro h_even
        simp [implementation]
        sorry