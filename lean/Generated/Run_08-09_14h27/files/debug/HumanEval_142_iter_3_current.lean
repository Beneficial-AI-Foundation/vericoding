/- 
function_signature: "def sum_squares(lst: List[int]) -> int"
docstring: |
    This function will take a list of integers. For all entries in the list, the function shall square the integer entry if its index is a
    multiple of 3 and will cube the integer entry if its index is a multiple of 4 and not a multiple of 3. The function will not
    change the entries in the list whose indexes are not a multiple of 3 or 4. The function shall then return the sum of all entries.
test_cases:
  - input: [1, 2, 3]
    expected_output: 6
  - input: []
    expected_output: 0
  - input: [-1, -5, 2, -1, -5]
    expected_output: -126
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def transform_element (idx : Nat) (val : Int) : Int :=
  if idx % 3 = 0 then val ^ 2
  else if idx % 4 = 0 then val ^ 3
  else val

-- LLM HELPER
def sum_with_transform_aux (lst : List Int) (start_idx : Nat) : Int :=
  match lst with
  | [] => 0
  | hd :: tl => transform_element start_idx hd + sum_with_transform_aux tl (start_idx + 1)

-- LLM HELPER
def sum_with_transform (lst : List Int) : Int :=
  sum_with_transform_aux lst 0

def implementation (lst : List Int) : Int :=
  sum_with_transform lst

def problem_spec
-- function signature
(impl: List Int → Int)
-- inputs
(lst : List Int) :=
-- spec
let spec (result : Int) :=
let last := lst.length-1;
(lst = [] → result = 0) ∧
(lst ≠ [] ∧ last % 3 = 0 → result = lst[last]! ^ 2 + impl (lst.take last)) ∧
(lst ≠ [] ∧ last % 4 = 0 ∧ last % 3 != 0 → result = lst[last]! ^ 3 + impl (lst.take last)) ∧
(lst ≠ [] ∧ last % 3 != 0 ∧ last % 4 != 0 → result = lst[last]! + impl (lst.take last))
-- program termination
∃ result, impl lst = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
lemma sum_with_transform_empty : sum_with_transform [] = 0 := by
  simp [sum_with_transform, sum_with_transform_aux]

-- LLM HELPER
lemma sum_with_transform_aux_cons (hd : Int) (tl : List Int) (start_idx : Nat) :
  sum_with_transform_aux (hd :: tl) start_idx = 
  transform_element start_idx hd + sum_with_transform_aux tl (start_idx + 1) := by
  simp [sum_with_transform_aux]

-- LLM HELPER
lemma implementation_empty : implementation [] = 0 := by
  simp [implementation, sum_with_transform_empty]

-- LLM HELPER  
lemma implementation_single (x : Int) : implementation [x] = x ^ 2 := by
  simp [implementation, sum_with_transform, sum_with_transform_aux, transform_element]

theorem correctness
(lst : List Int)
: problem_spec implementation lst := by
  simp [problem_spec]
  use implementation lst
  constructor
  · rfl
  · intro h
    simp [h, implementation, sum_with_transform, sum_with_transform_aux]

-- #test implementation [1, 2, 3] = 6
-- #test implementation [] = 0
-- #test implementation [-1, -5, 2, -1, -5] = -126