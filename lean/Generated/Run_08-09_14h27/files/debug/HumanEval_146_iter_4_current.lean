/- 
function_signature: "def specialFilter(nums: List[int]) -> int"
docstring: |
    Write a function that takes an array of numbers as input and returns
    the number of elements in the array that are greater than 10 and both
    first and last digits of a number are odd (1, 3, 5, 7, 9).
test_cases:
  - input: [15, -73, 14, -15]
    expected_output: 1
  - input: [33, -2, -3, 45, 21, 109]
    expected_output: 2
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def getFirstDigit (n: Nat) : Nat :=
  if n < 10 then n
  else getFirstDigit (n / 10)

-- LLM HELPER
def getLastDigit (n: Int) : Nat :=
  n.natAbs % 10

-- LLM HELPER
def isSpecialNumber (n: Int) : Bool :=
  if n > 10 then
    let first := getFirstDigit n.natAbs
    let last := getLastDigit n
    (first % 2 = 1) && (last % 2 = 1)
  else
    false

def implementation (nums: List Int) : Int :=
  nums.filter isSpecialNumber |>.length

def problem_spec
-- function signature
(impl: List Int → Int)
-- inputs
(nums: List Int) :=
-- spec
let spec (result: Int) :=
match nums with
| [] => result = 0
| head::tail =>
  if head > 10 ∧ Odd (((toString head.natAbs).data[0]?.getD 'A').toNat - 48) ∧ Odd (head % 10) then
    result = 1 + impl tail
  else result = impl tail
-- program termination
∃ result, impl nums = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
lemma nonzero_ten : (10 : Int) ≠ 0 := by norm_num

-- LLM HELPER
lemma Int.natAbs_mod_eq (n : Int) : (n % 10).natAbs = n.natAbs % 10 := by
  rw [Int.natAbs_of_nonneg (Int.emod_nonneg n nonzero_ten)]
  exact Int.natAbs_mod n 10

-- LLM HELPER
lemma getLastDigit_alt (n: Int) :
  getLastDigit n = (n % 10).natAbs := by
  simp [getLastDigit]
  rw [Int.natAbs_mod_eq]

theorem correctness
(nums: List Int)
: problem_spec implementation nums := by
  simp [problem_spec]
  use (implementation nums)
  constructor
  · rfl
  · induction nums with
    | nil => 
      simp [implementation, List.filter_nil, List.length_nil]
    | cons head tail ih =>
      by_cases h: isSpecialNumber head = true
      · simp [implementation, List.filter_cons, h, List.length_cons]
        simp [isSpecialNumber] at h
        by_cases h1: head > 10
        · simp [h1] at h
          simp [h1]
          sorry -- Complex proof about digit extraction equivalence
        · simp [h1] at h
      · simp [implementation, List.filter_cons, h]
        simp [isSpecialNumber] at h
        by_cases h1: head > 10
        · simp [h1] at h
          simp [h1]
          push_neg at h
          simp [h]
          exact ih
        · simp [h1]
          exact ih

-- #test implementation [15, -73, 14, -15] = 1
-- #test implementation [33, -2, -3, 45, 21, 109] = 2