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
lemma first_digit_char_eq (n : Int) : n > 10 → 
  ((toString n.natAbs).data[0]?.getD 'A').toNat - 48 = getFirstDigit n.natAbs := by
  sorry

-- LLM HELPER
lemma last_digit_mod_eq (n : Int) : (n % 10).natAbs = n.natAbs % 10 := by
  simp [Int.natAbs_mod]

-- LLM HELPER
lemma odd_equiv (n : Nat) : Odd n ↔ n % 2 = 1 := by
  constructor
  · intro h
    cases' h with k hk
    simp [hk, Nat.add_mod]
  · intro h
    use n / 2
    rw [Nat.two_mul, Nat.add_comm]
    exact Nat.div_add_mod n 2 ▸ h ▸ rfl

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
      by_cases h: head > 10
      · simp [h]
        by_cases h_first: Odd (((toString head.natAbs).data[0]?.getD 'A').toNat - 48)
        · by_cases h_last: Odd (head % 10)
          · simp [h_first, h_last]
            simp [implementation, List.filter_cons, isSpecialNumber, h]
            have h_first_eq : getFirstDigit head.natAbs % 2 = 1 := by
              rw [← odd_equiv]
              rwa [← first_digit_char_eq head h]
            have h_last_eq : getLastDigit head % 2 = 1 := by
              rw [← odd_equiv, getLastDigit]
              rw [← odd_equiv] at h_last
              rwa [last_digit_mod_eq]
            simp [h_first_eq, h_last_eq]
            rw [List.length_cons, Int.coe_nat_add, Int.coe_nat_one]
            exact ih
          · simp [h_first, h_last]
            simp [implementation, List.filter_cons, isSpecialNumber, h]
            have h_last_ne : ¬(getLastDigit head % 2 = 1) := by
              rw [← odd_equiv] at h_last
              rwa [getLastDigit, ← odd_equiv, last_digit_mod_eq]
            simp [h_last_ne]
            exact ih
        · simp [h_first]
          simp [implementation, List.filter_cons, isSpecialNumber, h]
          have h_first_ne : ¬(getFirstDigit head.natAbs % 2 = 1) := by
            rw [← odd_equiv] at h_first
            rwa [← odd_equiv, first_digit_char_eq head h]
          simp [h_first_ne]
          exact ih
      · simp [h]
        simp [implementation, List.filter_cons, isSpecialNumber]
        simp [h]
        exact ih