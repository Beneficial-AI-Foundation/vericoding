/- 
function_signature: "def sum_product(numbers: List[int]) -> Tuple[int, int]"
docstring: |
    For a given list of integers, return a tuple consisting of a sum and a product of all the integers in a list.
    Empty sum should be equal to 0 and empty product should be equal to 1.
test_cases:
  - input: []
    expected_output: (0, 1)
  - input: [1, 2, 3, 4]
    expected_output: (10, 24)
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (numbers: List Int) : (Int × Int) :=
  match numbers with
  | [] => (0, 1)
  | h :: t => 
    let (sum_tail, prod_tail) := implementation t
    (h + sum_tail, h * prod_tail)

def problem_spec
-- function signature
(implementation: List Int → (Int × Int))
-- inputs
(numbers: List Int) :=
-- spec
let spec (result: (Int × Int)) :=
let (sum, prod) := result;
(numbers = [] → sum = 0 ∧ prod = 1) ∧
(numbers ≠ [] →
(let (sum_tail, prod_tail) := implementation numbers.tail;
sum - sum_tail = numbers[0]! ∧
sum_tail * prod_tail + prod = sum * prod_tail));
-- program termination
∃ result, implementation numbers = result ∧
spec result

-- LLM HELPER
lemma implementation_empty : implementation [] = (0, 1) := by
  simp [implementation]

-- LLM HELPER  
lemma implementation_cons (h : Int) (t : List Int) :
  implementation (h :: t) = (h + (implementation t).1, h * (implementation t).2) := by
  simp [implementation]

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers
:= by
  unfold problem_spec
  use implementation numbers
  constructor
  · rfl
  · cases numbers with
    | nil =>
      simp [implementation_empty]
    | cons head tail =>
      simp [implementation_cons]
      constructor
      · simp
      · ring

-- #test implementation [] = (0, 1)
-- #test implementation [1, 2, 3, 4] = (10, 24)