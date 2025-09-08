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
  (n.natAbs % 10).toNat

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
  let first_digit := (toString head.natAbs).toList[0]!.toNat - Char.toNat '0';
  let last_digit := head % 10;
  let valid := head > 10 ∧ Odd first_digit ∧ Odd last_digit
  if valid then result = 1 + impl tail else result = impl tail
-- program termination
∃ result, impl nums = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
lemma getFirstDigit_correct (n: Nat) : 
  n > 0 → getFirstDigit n = (toString n).toList[0]!.toNat - Char.toNat '0' := by
  intro h
  sorry

-- LLM HELPER  
lemma getLastDigit_correct (n: Int) :
  getLastDigit n = (n % 10).natAbs := by
  simp [getLastDigit]
  sorry

-- LLM HELPER
lemma isSpecialNumber_correct (n: Int) :
  isSpecialNumber n = true ↔ 
  (n > 10 ∧ Odd (getFirstDigit n.natAbs) ∧ Odd (getLastDigit n)) := by
  simp [isSpecialNumber]
  constructor
  · intro h
    sorry
  · intro h
    sorry

theorem correctness
(nums: List Int)
: problem_spec implementation nums := by
  simp [problem_spec]
  use (implementation nums)
  constructor
  · rfl
  · induction nums with
    | nil => 
      simp [implementation]
    | cons head tail ih =>
      simp [implementation]
      sorry

-- #test implementation [15, -73, 14, -15] = 1
-- #test implementation [33, -2, -3, 45, 21, 109] = 2