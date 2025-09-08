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

-- LLM HELPER
def sum_odd_at_even_positions_aux (lst: List Int) (idx: Nat) : Int :=
  match lst with
  | [] => 0
  | h :: t =>
    if idx % 2 = 0 then
      if h % 2 = 1 then h + sum_odd_at_even_positions_aux t (idx + 1)
      else sum_odd_at_even_positions_aux t (idx + 1)
    else
      sum_odd_at_even_positions_aux t (idx + 1)

def implementation (lst: List Int) : Int :=
  sum_odd_at_even_positions_aux lst 0

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

-- LLM HELPER
lemma implementation_eq_aux : ∀ lst, implementation lst = sum_odd_at_even_positions_aux lst 0 :=
  fun lst => rfl

-- LLM HELPER  
lemma sum_odd_at_even_positions_aux_correct (lst: List Int) (start_idx: Nat) :
  sum_odd_at_even_positions_aux lst start_idx = 
  (List.range lst.length).foldl (fun acc i => 
    if (start_idx + i) % 2 = 0 ∧ lst[i]! % 2 = 1 then acc + lst[i]! else acc) 0 := by
  induction lst generalizing start_idx with
  | nil => simp [sum_odd_at_even_positions_aux]
  | cons h t ih =>
    simp [sum_odd_at_even_positions_aux]
    by_cases h1 : start_idx % 2 = 0
    · by_cases h2 : h % 2 = 1
      · simp [h1, h2]
        rw [ih (start_idx + 1)]
        simp
      · simp [h1, h2]
        rw [ih (start_idx + 1)]
        simp
    · simp [h1]
      rw [ih (start_idx + 1)]
      simp

theorem correctness
(lst: List Int)
: problem_spec implementation lst := by
  use implementation lst
  constructor
  · rfl
  · intro h_nonempty i h_i
    constructor
    · intro h_len_one
      simp [implementation, sum_odd_at_even_positions_aux]
      cases lst with
      | nil => contradiction
      | cons h t =>
        simp at h_len_one
        simp [h_len_one, sum_odd_at_even_positions_aux]
    · intro h_bound
      constructor
      · intro h_odd
        simp [implementation]
        sorry
      · intro h_even
        simp [implementation]
        sorry

-- #test implementation ([5, 8, 7, 1]: List Int) = 12
-- #test implementation ([3, 3, 3, 3, 3]: List Int) = 9
-- #test implementation ([30, 13, 24, 321]: List Int) = 0