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
  (numbers.sum, numbers.prod)

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
lemma list_sum_nil : ([] : List Int).sum = 0 := by simp

-- LLM HELPER
lemma list_prod_nil : ([] : List Int).prod = 1 := by simp

-- LLM HELPER
lemma list_sum_cons (x : Int) (xs : List Int) : (x :: xs).sum = x + xs.sum := by simp

-- LLM HELPER
lemma list_prod_cons (x : Int) (xs : List Int) : (x :: xs).prod = x * xs.prod := by simp

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers
:= by
  unfold problem_spec implementation
  use (numbers.sum, numbers.prod)
  simp
  constructor
  · intro h
    constructor
    · rw [h]
      exact list_sum_nil
    · rw [h] 
      exact list_prod_nil
  · intro h
    cases' numbers with head tail
    · contradiction
    · simp [List.getElem_cons_zero]
      constructor
      · rw [list_sum_cons]
        ring
      · have h1 : (head :: tail).prod = head * tail.prod := list_prod_cons head tail
        have h2 : implementation tail = (tail.sum, tail.prod) := rfl
        simp [h1, h2]
        ring

-- #test implementation [] = (0, 1)
-- #test implementation [1, 2, 3, 4] = (10, 24)