/- 
function_signature: "def rolling_max(numbers: List[int]) -> Tuple[int, int]"
docstring: |
  From a given list of integers, generate a list of rolling maximum element found until given moment
  in the sequence.
test_cases:
  - input: [1, 2, 3, 2, 3, 4, 2]
    expected_output: [1, 2, 3, 3, 3, 4, 4]
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def rolling_max_aux (numbers: List Int) (current_max: Int) : List Int :=
  match numbers with
  | [] => []
  | head :: tail =>
    let new_max := max current_max head
    new_max :: rolling_max_aux tail new_max

def implementation (numbers: List Int) : List Int :=
  match numbers with
  | [] => []
  | head :: tail => head :: rolling_max_aux tail head

def problem_spec
-- function signature
(implementation: List Int → List Int)
-- inputs
(numbers: List Int) :=
-- spec
let spec (result: List Int) :=
result.length = numbers.length ∧
∀ i, i < numbers.length →
(result[i]?.getD 0 ∈ numbers.take (i + 1) ∧
∀ j, j ≤ i → numbers[j]?.getD 0 ≤ result[i]?.getD 0);
-- program termination
∃ result, implementation numbers = result ∧
spec result

-- LLM HELPER
lemma rolling_max_aux_length (numbers: List Int) (current_max: Int) :
  (rolling_max_aux numbers current_max).length = numbers.length := by
  induction numbers generalizing current_max with
  | nil => simp [rolling_max_aux]
  | cons head tail ih => 
    simp [rolling_max_aux]
    exact ih (max current_max head)

-- LLM HELPER
lemma implementation_length (numbers: List Int) :
  (implementation numbers).length = numbers.length := by
  cases numbers with
  | nil => simp [implementation]
  | cons head tail => 
    simp [implementation]
    exact rolling_max_aux_length tail head

-- LLM HELPER
lemma max_cases (a b : Int) : max a b = a ∨ max a b = b := by
  simp [max_def]
  by_cases h : a ≤ b
  · right; exact if_pos h
  · left; exact if_neg (not_le.mp h)

-- LLM HELPER
lemma rolling_max_aux_bounds (numbers: List Int) (current_max: Int) (i: Nat)
  (hi: i < numbers.length) :
  current_max ≤ (rolling_max_aux numbers current_max)[i]?.getD 0 := by
  induction numbers generalizing current_max i with
  | nil => simp at hi
  | cons head tail ih =>
    simp [rolling_max_aux]
    cases i with
    | zero =>
      simp
      exact le_max_left current_max head
    | succ i' =>
      simp at hi ⊢
      exact ih (max current_max head) i' hi

-- LLM HELPER
lemma rolling_max_aux_monotonic (numbers: List Int) (current_max: Int) (i j: Nat)
  (hi: i < numbers.length) (hj: j ≤ i) :
  numbers[j]?.getD 0 ≤ (rolling_max_aux numbers current_max)[i]?.getD 0 := by
  induction numbers generalizing current_max i j with
  | nil => simp at hi
  | cons head tail ih =>
    simp [rolling_max_aux]
    cases i with
    | zero =>
      simp at hj
      simp [hj]
      exact le_max_right current_max head
    | succ i' =>
      simp at hi ⊢
      cases j with
      | zero =>
        simp
        have h_bounds := rolling_max_aux_bounds tail (max current_max head) i' hi
        have h_le_max := le_max_right current_max head
        exact le_trans h_le_max h_bounds
      | succ j' =>
        simp
        exact ih (max current_max head) i' hi j' (Nat.succ_le_succ_iff.mp hj)

-- LLM HELPER
lemma rolling_max_aux_in_list (numbers: List Int) (current_max: Int) (i: Nat)
  (hi: i < numbers.length) :
  (rolling_max_aux numbers current_max)[i]?.getD 0 ∈ numbers.take numbers.length ∨ 
  (rolling_max_aux numbers current_max)[i]?.getD 0 = current_max := by
  induction numbers generalizing current_max i with
  | nil => simp at hi
  | cons head tail ih =>
    simp [rolling_max_aux]
    cases i with
    | zero =>
      simp
      cases max_cases current_max head with
      | inl h => simp [h]; right; rfl
      | inr h => simp [h]; left; simp [List.take]; left; rfl
    | succ i' =>
      simp at hi ⊢
      have h_ih := ih (max current_max head) i' hi
      cases h_ih with
      | inl h1 => 
        left
        simp [List.take]
        exact List.mem_of_mem_tail h1
      | inr h2 =>
        simp [h2]
        cases max_cases current_max head with
        | inl h_max => 
          simp [h_max]
          right; rfl
        | inr h_max =>
          simp [h_max]
          left; simp [List.take]; left; rfl

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers
:= by
  simp [problem_spec]
  use implementation numbers
  constructor
  · rfl
  constructor
  · exact implementation_length numbers
  · intro i hi
    cases numbers with
    | nil => simp at hi
    | cons head tail =>
      simp [implementation] at hi ⊢
      cases i with
      | zero =>
        constructor
        · simp [List.take]; left; rfl
        · intro j hj
          simp at hj
          simp [hj]
      | succ i' =>
        simp at hi
        have h_aux_len := rolling_max_aux_length tail head
        simp [h_aux_len] at hi
        constructor
        · have h_mem := rolling_max_aux_in_list tail head i' hi
          cases h_mem with
          | inl h1 =>
            simp [List.take]
            right
            exact List.mem_take_of_mem (i' + 1) h1
          | inr h2 =>
            simp [List.take, h2]
            left; rfl
        · intro j hj
          cases j with
          | zero =>
            simp
            have h_bounds := rolling_max_aux_bounds tail head i' hi
            exact le_trans (le_max_left head (rolling_max_aux tail head)[i']?.getD 0)) h_bounds
          | succ j' =>
            simp
            exact rolling_max_aux_monotonic tail head i' hi j' (Nat.succ_le_succ_iff.mp hj)

-- #test implementation [1, 2, 3, 2, 3, 4, 2] = [1, 2, 3, 3, 3, 4, 4]