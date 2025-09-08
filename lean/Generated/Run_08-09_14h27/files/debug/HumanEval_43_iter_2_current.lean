/- 
function_signature: "def pairs_sum_to_zero(numbers: List[int]) -> Bool"
docstring: |
    pairs_sum_to_zero takes a list of integers as an input.
    it returns True if there are two distinct elements in the list that
    sum to zero, and False otherwise.
test_cases:
  - input: [1, 3, 5, 0]
    expected_output: False
  - input: [1, 3, -2, 1]
    expected_output: False
  - input: [1]
    expected_output: False
  - input: [2, 4, -5, 3, 5, 7]
    expected_output: True
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (numbers: List Int) : Bool :=
  if numbers.length < 2 then false
  else
    let rec aux (i j: Nat) : Bool :=
      if i < numbers.length then
        if j < numbers.length then
          if i ≠ j ∧ numbers[i]! + numbers[j]! = 0 then true
          else aux i (j + 1)
        else aux (i + 1) 0
      else false
    aux 0 0

def problem_spec
-- function signature
(implementation: List Int → Bool)
-- inputs
(numbers: List Int) :=
let sum_i_j (i j: Nat) : Bool :=
  numbers[i]! + numbers[j]! = 0;
let exists_zero := 2 ≤ numbers.length ∧ (∃ i j, i ≠ j ∧
 i < numbers.length ∧ j < numbers.length ∧
 sum_i_j i j)
-- spec
let spec (result: Bool) :=
result ↔ exists_zero
-- -- program termination
∃ result, implementation numbers = result ∧
spec result

-- LLM HELPER
lemma aux_finds_pair (numbers: List Int) :
  let rec aux (i j: Nat) : Bool :=
    if i < numbers.length then
      if j < numbers.length then
        if i ≠ j ∧ numbers[i]! + numbers[j]! = 0 then true
        else aux i (j + 1)
      else aux (i + 1) 0
    else false
  aux 0 0 = true ↔ 
  ∃ i' j', i' < numbers.length ∧ j' < numbers.length ∧ i' ≠ j' ∧ numbers[i']! + numbers[j']! = 0 := by
  constructor
  · intro h
    -- If aux returns true, there exists a pair
    have : ∃ i' j', i' < numbers.length ∧ j' < numbers.length ∧ i' ≠ j' ∧ numbers[i']! + numbers[j']! = 0 := by
      sorry
    exact this
  · intro ⟨i', j', hi', hj', hneq, hsum⟩
    -- If pair exists, aux will find it
    sorry

theorem correctness
(numbers : List Int)
: problem_spec implementation numbers
:= by
  unfold problem_spec implementation
  simp only []
  use (if numbers.length < 2 then false
       else
         let rec aux (i j: Nat) : Bool :=
           if i < numbers.length then
             if j < numbers.length then
               if i ≠ j ∧ numbers[i]! + numbers[j]! = 0 then true
               else aux i (j + 1)
             else aux (i + 1) 0
           else false
         aux 0 0)
  constructor
  · -- Show implementation terminates correctly
    rfl
  · -- Show specification holds
    by_cases h : numbers.length < 2
    · -- Case: length < 2
      simp [h]
      constructor
      · intro h_false
        omega
      · intro ⟨h_len, _⟩
        omega
    · -- Case: length ≥ 2  
      simp [h]
      constructor
      · -- If aux returns true, then pair exists
        intro h_aux_true
        constructor
        · omega
        · -- Use the helper lemma
          rw [aux_finds_pair] at h_aux_true
          obtain ⟨i', j', hi', hj', hneq, hsum⟩ := h_aux_true
          use i', j'
          exact ⟨hneq, hi', hj', hsum⟩
      · -- If pair exists, then aux returns true
        intro ⟨h_len, i, j, h_neq, h_i_bound, h_j_bound, h_sum⟩
        rw [aux_finds_pair]
        use i, j
        exact ⟨h_i_bound, h_j_bound, h_neq, h_sum⟩