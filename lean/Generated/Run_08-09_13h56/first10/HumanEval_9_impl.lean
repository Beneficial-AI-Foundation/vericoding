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
      have h_bounds := ih (max current_max head) i' hi
      have le_trans : current_max ≤ max current_max head := le_max_left current_max head
      exact le_trans.trans h_bounds

-- LLM HELPER
lemma rolling_max_aux_in_list (numbers: List Int) (current_max: Int) (i: Nat)
  (hi: i < numbers.length) :
  (rolling_max_aux numbers current_max)[i]?.getD 0 = current_max ∨ 
  (rolling_max_aux numbers current_max)[i]?.getD 0 ∈ numbers.take (i + 1) := by
  induction numbers generalizing current_max i with
  | nil => simp at hi
  | cons head tail ih =>
    simp [rolling_max_aux]
    cases i with
    | zero =>
      simp [List.take]
      by_cases h : current_max ≤ head
      · simp [max_def, h]
        right; left; rfl
      · simp [max_def, h]
        left; rfl
    | succ i' =>
      simp at hi ⊢
      have ih_res := ih (max current_max head) i' hi
      simp [List.take]
      cases ih_res with
      | inl h => 
        by_cases h' : current_max ≤ head
        · simp [max_def, h'] at h
          right; exact h
        · simp [max_def, h'] at h
          left; exact h
      | inr h => right; right; exact h

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
  intro i hi
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
      · have h_in := rolling_max_aux_in_list tail head i' hi
        simp [List.take]
        cases h_in with
        | inl h => right; exact h
        | inr h => right; right; exact h
      · intro j hj
        cases j with
        | zero =>
          simp
          have h_bounds := rolling_max_aux_bounds tail head i' hi
          exact h_bounds
        | succ j' =>
          simp at hj
          have hj' : j' < tail.length := by simp at hj; exact Nat.lt_of_succ_lt_succ hj
          -- Use a simpler approach by leveraging the fact that rolling max is monotonic
          have h_monotonic : ∀ k l, k ≤ l → l < tail.length → 
            (rolling_max_aux tail head)[k]?.getD 0 ≤ (rolling_max_aux tail head)[l]?.getD 0 := by
            intro k l hkl hl
            -- This follows from the fact that rolling max is non-decreasing
            -- We'll use induction on the structure
            induction tail generalizing head k l with
            | nil => simp at hl
            | cons t_head t_tail t_ih =>
              simp [rolling_max_aux]
              cases k with
              | zero =>
                cases l with
                | zero => simp
                | succ l' =>
                  simp
                  have h_bounds := rolling_max_aux_bounds t_tail (max head t_head) l' (by simp at hl; exact Nat.lt_of_succ_lt_succ hl)
                  exact le_max_left head t_head |>.trans h_bounds
              | succ k' =>
                cases l with
                | zero => simp at hkl
                | succ l' =>
                  simp at hkl hl
                  exact t_ih (max head t_head) k' l' (Nat.le_of_succ_le_succ hkl) (Nat.lt_of_succ_lt_succ hl)
          exact h_monotonic j' i' (Nat.le_of_succ_le_succ hj) hi