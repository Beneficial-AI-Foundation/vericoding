/- 
function_signature: "def double_the_difference(numbers: List[float]) -> Int"
docstring: |
    Given a list of numbers, return the sum of squares of the numbers
    in the list that are odd. Ignore numbers that are negative or not integers.
test_cases:
  - input: [1, 3, 2, 0]
    expected_output: 10
  - input: [-1. -2, 0]
    expected_output: 0
  - input: [9, -2]
    expected_output: 81
  - input: [0]
    expected_output: 0
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def isOddInteger (n : Rat) : Bool :=
  n.isInt && n ≥ 0 && (n.floor % 2 = 1)

def implementation (numbers: List Rat) : Int :=
  numbers.foldl (fun acc n => 
    if isOddInteger n then acc + n.floor ^ 2 else acc) 0

def problem_spec
-- function signature
(impl: List Rat → Int)
-- inputs
(numbers: List Rat) :=
let isEven (n : Rat) := n % 2 = 0;
let isNegative (n : Rat) := n < 0;
let isNotInteger (n : Rat) := ¬ n.isInt;
-- spec
let spec (result: Int) :=
0 < numbers.length →
0 ≤ result ∧
if numbers.length = 1
then result = if (isEven numbers[0]! ∨ isNegative numbers[0]! ∨ isNotInteger numbers[0]!) then (0 : Int) else numbers[0]!.floor ^ 2
else result = if (isEven numbers[0]! ∨ isNegative numbers[0]! ∨ isNotInteger numbers[0]!) then (0 : Int) else numbers[0]!.floor ^ 2 + impl numbers.tail
-- program terminates
∃ result, impl numbers = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
lemma foldl_nonneg (numbers : List Rat) :
  0 ≤ numbers.foldl (fun acc n => 
    if isOddInteger n then acc + n.floor ^ 2 else acc) 0 := by
  induction numbers with
  | nil => simp
  | cons h t ih =>
    simp [List.foldl]
    by_cases h_case : isOddInteger h
    · simp [h_case]
      have h_pos : 0 ≤ h.floor ^ 2 := sq_nonneg _
      have acc_nonneg : 0 ≤ t.foldl (fun acc n => if isOddInteger n = true then acc + n.floor ^ 2 else acc) 0 := ih
      -- Apply the monotonicity of foldl instead of trying to rewrite addition
      have : t.foldl (fun acc n => if isOddInteger n = true then acc + n.floor ^ 2 else acc) (h.floor ^ 2) 
           = h.floor ^ 2 + t.foldl (fun acc n => if isOddInteger n = true then acc + n.floor ^ 2 else acc) 0 := by
        exact List.foldl_add_comm _ _ _
      rw [this]
      exact add_nonneg h_pos acc_nonneg
    · simp [h_case]
      exact ih

-- LLM HELPER
lemma implementation_eq_foldl (numbers : List Rat) :
  implementation numbers = numbers.foldl (fun acc n => 
    if isOddInteger n then acc + n.floor ^ 2 else acc) 0 := by
  rfl

-- LLM HELPER
lemma isOddInteger_iff (n : Rat) :
  isOddInteger n = true ↔ n.isInt = true ∧ n ≥ 0 ∧ n.floor % 2 = 1 := by
  constructor
  · intro h
    exact ⟨by simp [isOddInteger] at h; exact h.1, 
           by simp [isOddInteger] at h; exact h.2.1,
           by simp [isOddInteger] at h; exact h.2.2⟩
  · intro ⟨h1, h2, h3⟩
    simp [isOddInteger, h1, h2, h3]

theorem correctness
(numbers: List Rat)
: problem_spec implementation numbers := by
  unfold problem_spec
  simp only [implementation_eq_foldl]
  use numbers.foldl (fun acc n => if isOddInteger n then acc + n.floor ^ 2 else acc) 0
  constructor
  · rfl
  · intro h_nonempty
    constructor
    · exact foldl_nonneg numbers
    · by_cases h_len : numbers.length = 1
      · simp [h_len]
        cases numbers with
        | nil => simp at h_len
        | cons head tail =>
          simp at h_len
          simp [h_len, List.foldl]
          by_cases h_case : isOddInteger head
          · simp [h_case]
            have ⟨h_int, h_nonneg, h_odd⟩ := (isOddInteger_iff head).mp h_case
            simp [h_int] at h_nonneg ⊢
            cases h_nonneg with
            | inl h_zero => 
              simp [h_zero] at h_odd
              simp [h_odd]
            | inr h_pos => 
              simp [show ¬(head < 0) from not_lt.mpr (le_of_lt h_pos)]
              exact h_odd
          · simp [h_case]
            rw [isOddInteger_iff] at h_case
            push_neg at h_case
            cases h_case with
            | inl h => simp [h]
            | inr h => 
              cases h with
              | inl h_neg => simp [h_neg]
              | inr h_even => simp [h_even]
      · simp [h_len]
        sorry

-- #test implementation ([1, 3, 2, 0]: List Rat) = (10: Int)
-- #test implementation ([-1, -2, 0]: List Int) = (0: Int)
-- #test implementation ([9, -2]: List Int) = 81
-- #test implementation ([0]: List Int) = 0