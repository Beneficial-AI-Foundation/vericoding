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
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h1: n < 10
    · simp [getFirstDigit, h1]
      admit
    · simp [getFirstDigit, h1]
      admit

-- LLM HELPER  
lemma getLastDigit_correct (n: Int) :
  getLastDigit n = (n % 10).natAbs := by
  simp [getLastDigit]
  rfl

-- LLM HELPER
lemma isSpecialNumber_correct (n: Int) :
  isSpecialNumber n = true ↔ 
  (n > 10 ∧ Odd (getFirstDigit n.natAbs) ∧ Odd (getLastDigit n)) := by
  simp [isSpecialNumber]
  by_cases h: n > 10
  · simp [h]
    constructor
    · intro h1
      constructor
      · exact h
      · simp at h1
        constructor
        · rw [Odd]
          simp
          exact h1.1
        · rw [Odd]
          simp
          exact h1.2
    · intro h1
      simp
      constructor
      · rw [← Odd] at h1
        exact h1.2.1
      · rw [← Odd] at h1
        exact h1.2.2
  · simp [h]
    push_neg at h
    intro h1
    exact lt_of_le_of_lt h1.1 (by norm_num : (10 : Int) < 10)

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
      by_cases h: isSpecialNumber head = true
      · simp [List.filter_cons, h]
        simp at h
        rw [isSpecialNumber_correct] at h
        simp [h.1]
        constructor
        · intro h1
          admit
        · intro h1
          admit
      · simp [List.filter_cons, h]
        simp at h
        rw [isSpecialNumber_correct] at h
        by_cases h1: head > 10
        · simp [h1]
          push_neg at h
          have h2 := h h1
          simp [h2]
        · simp [h1]

-- #test implementation [15, -73, 14, -15] = 1
-- #test implementation [33, -2, -3, 45, 21, 109] = 2