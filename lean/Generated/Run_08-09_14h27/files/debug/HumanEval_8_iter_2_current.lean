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
  (numbers.sum, numbers.foldl (· * ·) 1)

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
lemma list_sum_nil : ([] : List Int).sum = 0 := by simp [List.sum]

-- LLM HELPER
lemma list_foldl_mul_nil : List.foldl (· * ·) 1 ([] : List Int) = 1 := by simp

-- LLM HELPER
lemma list_sum_cons (h : Int) (t : List Int) : (h :: t).sum = h + t.sum := by simp [List.sum]

-- LLM HELPER
lemma list_foldl_mul_cons (h : Int) (t : List Int) : 
  List.foldl (· * ·) 1 (h :: t) = h * List.foldl (· * ·) 1 t := by 
  induction t with
  | nil => simp
  | cons a as ih => 
    simp [List.foldl]
    rw [← ih]
    ring

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers
:= by
  unfold problem_spec
  use implementation numbers
  constructor
  · rfl
  · unfold implementation
    cases' numbers with h t
    · -- Case: numbers = []
      simp
      constructor
      · intro
        constructor
        · exact list_sum_nil
        · exact list_foldl_mul_nil
      · intro h_contra
        exact False.elim (h_contra rfl)
    · -- Case: numbers = h :: t
      simp
      constructor
      · intro h_contra
        exact False.elim h_contra
      · intro
        unfold implementation
        simp [List.sum, List.tail]
        have h1 : (h :: t).sum = h + t.sum := list_sum_cons h t
        have h2 : List.foldl (· * ·) 1 (h :: t) = h * List.foldl (· * ·) 1 t := list_foldl_mul_cons h t
        simp [h1, h2]
        ring

-- #test implementation [] = (0, 1)
-- #test implementation [1, 2, 3, 4] = (10, 24)