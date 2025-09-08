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

-- LLM HELPER
def check_pairs_aux (numbers: List Int) (i: Nat) (j: Nat) : Bool :=
  if h1 : i < numbers.length then
    if h2 : j < numbers.length then
      if i ≠ j ∧ numbers[i]! + numbers[j]! = 0 then true
      else false
    else false
  else false

-- LLM HELPER  
def find_pair (numbers: List Int) (i: Nat) : Bool :=
  if i < numbers.length then
    let rec check_with_others (j: Nat) : Bool :=
      if j < numbers.length then
        if i ≠ j ∧ numbers[i]! + numbers[j]! = 0 then true
        else if j + 1 < numbers.length then check_with_others (j + 1)
        else false
      else false
    check_with_others 0
  else false

-- LLM HELPER
def find_any_pair (numbers: List Int) (i: Nat) : Bool :=
  if i < numbers.length then
    if find_pair numbers i then true
    else if i + 1 < numbers.length then find_any_pair numbers (i + 1)
    else false
  else false

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
lemma aux_correct (numbers: List Int) (i j: Nat) :
  let rec aux (i j: Nat) : Bool :=
    if i < numbers.length then
      if j < numbers.length then
        if i ≠ j ∧ numbers[i]! + numbers[j]! = 0 then true
        else aux i (j + 1)
      else aux (i + 1) 0
    else false
  aux i j = true ↔ ∃ i' j', i' ≥ i ∧ i' < numbers.length ∧ j' < numbers.length ∧ i' ≠ j' ∧ numbers[i']! + numbers[j']! = 0 := by
  sorry

theorem correctness
(numbers : List Int)
: problem_spec implementation numbers
:= by
  unfold problem_spec implementation
  simp only [exists_prop]
  constructor
  · -- Show implementation terminates and produces correct result
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
    · rfl
    · -- Show specification holds
      unfold List.get!
      by_cases h : numbers.length < 2
      · -- Case: length < 2
        simp [h]
        constructor
        · intro h_contra
          exfalso
          exact h_contra
        · intro ⟨h_len, i, j, h_neq, h_i_bound, h_j_bound, h_sum⟩
          exfalso
          omega
      · -- Case: length ≥ 2  
        simp [h]
        constructor
        · -- If aux returns true, then pair exists
          intro h_aux_true
          constructor
          · omega
          · -- Need to show pair exists
            sorry
        · -- If pair exists, then aux returns true
          intro ⟨h_len, i, j, h_neq, h_i_bound, h_j_bound, h_sum⟩
          sorry