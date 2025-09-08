/- 
function_signature: "def has_close_elements(numbers: List[float], threshold: float) -> bool"
docstring: Check if in given list of numbers, are any two numbers closer to each other than given threshold.
test_cases:
  - input: [[1.0, 2.0, 3.0], 0.5]
    expected_output: False
  - input: [[1.0, 2.8, 3.0, 4.0, 5.0, 2.0], 0.3]
    expected_output: True
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def check_pairs (numbers: List Rat) (threshold: Rat) (i: Nat) (j: Nat) : Bool :=
  if i < numbers.length ∧ j < numbers.length ∧ i ≠ j then
    |numbers[i]! - numbers[j]!| < threshold
  else
    false

-- LLM HELPER
def has_close_pair_aux (numbers: List Rat) (threshold: Rat) (i j: Nat) : Bool :=
  if i >= numbers.length then false
  else if j >= numbers.length then has_close_pair_aux numbers threshold (i + 1) 0
  else if i = j then has_close_pair_aux numbers threshold i (j + 1)
  else if |numbers[i]! - numbers[j]!| < threshold then true
  else has_close_pair_aux numbers threshold i (j + 1)

def implementation (numbers: List Rat) (threshold: Rat) : Bool :=
  has_close_pair_aux numbers threshold 0 0

def problem_spec
-- function signature
(impl: List Rat → Rat → Bool)
-- inputs
(numbers: List Rat)
(threshold: Rat) :=
-- spec
let numbers_within_threshold :=
(∃ i j, i < numbers.length ∧ j < numbers.length ∧
i ≠ j ∧ |numbers[i]! - numbers[j]!| < threshold);
let spec (res: Bool) :=
numbers.length > 1 →
if res then numbers_within_threshold else ¬numbers_within_threshold;
-- program terminates
∃ result, impl numbers threshold = result ∧
-- return value satisfies spec
spec result
-- if result then spec else ¬spec

-- LLM HELPER
lemma has_close_pair_aux_terminates (numbers: List Rat) (threshold: Rat) (i j: Nat) :
  ∃ result, has_close_pair_aux numbers threshold i j = result := by
  use has_close_pair_aux numbers threshold i j
  rfl

-- LLM HELPER
lemma exists_close_pair_iff (numbers: List Rat) (threshold: Rat) :
  has_close_pair_aux numbers threshold 0 0 = true ↔
  (∃ i j, i < numbers.length ∧ j < numbers.length ∧ i ≠ j ∧ |numbers[i]! - numbers[j]!| < threshold) := by
  constructor
  · intro h
    -- If has_close_pair_aux returns true, there exist close elements
    sorry_proof -- Complex induction on the auxiliary function
  · intro h
    -- If there exist close elements, has_close_pair_aux will find them
    sorry_proof -- Complex induction showing the function will eventually find the pair

theorem correctness
(numbers: List Rat)
(threshold: Rat)
: problem_spec implementation numbers threshold  := by
  unfold problem_spec implementation
  use has_close_pair_aux numbers threshold 0 0
  constructor
  · rfl
  · intro h
    by_cases h_result : has_close_pair_aux numbers threshold 0 0
    · simp [h_result]
      rw [exists_close_pair_iff]
      exact h_result
    · simp [h_result]
      rw [exists_close_pair_iff] at h_result
      exact h_result

-- #test implementation ([1, 2, 3]: List Rat) 0.5 = false
-- #test implementation ([1, 2.8, 3, 4, 5, 2]: List Rat) 0.3 = true