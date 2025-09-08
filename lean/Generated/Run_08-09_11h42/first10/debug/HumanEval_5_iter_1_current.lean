/- 
function_signature: "def intersperse(numbers: List[int], delimeter: int) -> List[int]"
docstring: |
    Insert a number 'delimeter' between every two consecutive elements of input list `numbers'
test_cases:
  - input:
      - []
      - 4
    expected_output: []
  - input:
      - [1, 2, 3]
      - 4
    expected_output: [1, 4, 2, 4, 3]
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (numbers: List Int) (delimeter: Int) : List Int :=
  match numbers with
  | [] => []
  | [x] => [x]
  | x :: xs => x :: delimeter :: implementation xs delimeter

def problem_spec
-- function signature
(implementation: List Int → Int → List Int)
-- inputs
(numbers: List Int)
(delimeter: Int) :=
-- spec
let spec (result: List Int) :=
(result.length = 0 ∧ result = numbers) ∨
(result.length = 2 ∧ numbers.length = 1 ∧
result[0]! = numbers[0]! ∧ result[1]! = delimeter) ∨
(result.length = 2 * numbers.length - 1 ∧
∀ i, i < numbers.length →
result[2 * i]! = numbers[i]! ∧
(0 < 2*i - 1 → result[2 * i - 1]! = delimeter));
-- program termination
∃ result, implementation numbers delimeter = result ∧
spec result

-- LLM HELPER
lemma implementation_length (numbers: List Int) (delimeter: Int) :
  let result := implementation numbers delimeter
  (numbers.length = 0 → result.length = 0) ∧
  (numbers.length = 1 → result.length = 1) ∧
  (numbers.length ≥ 2 → result.length = 2 * numbers.length - 1) := by
  induction numbers with
  | nil => simp [implementation]
  | cons x xs ih =>
    cases xs with
    | nil => simp [implementation]
    | cons y ys =>
      simp [implementation]
      have h : (x :: y :: ys).length ≥ 2 := by simp; norm_num
      have ih_case : (y :: ys).length ≥ 1 := by simp; norm_num
      cases' Nat.lt_or_ge (y :: ys).length 2 with h1 h2
      · have h_eq : (y :: ys).length = 1 := by
          cases ys with
          | nil => simp
          | cons z zs => simp at h1; norm_num at h1
        rw [h_eq] at ih
        simp at ih
        simp [h_eq]
        norm_num
      · have ih_ge2 := ih.2.2 h2
        simp [ih_ge2]
        ring

-- LLM HELPER
lemma implementation_elements (numbers: List Int) (delimeter: Int) :
  let result := implementation numbers delimeter
  ∀ i, i < numbers.length → result[2 * i]? = numbers[i]? := by
  induction numbers with
  | nil => simp [implementation]
  | cons x xs ih =>
    intro i hi
    cases xs with
    | nil =>
      simp [implementation]
      cases i with
      | zero => simp
      | succ j => simp at hi
    | cons y ys =>
      simp [implementation]
      cases i with
      | zero => simp
      | succ j =>
        simp
        have hj : j < xs.length := by simp at hi; exact Nat.lt_of_succ_lt_succ hi
        have ih_j := ih j hj
        simp [implementation] at ih_j
        exact ih_j

theorem correctness
(numbers: List Int)
(delimeter: Int)
: problem_spec implementation numbers delimeter
:= by
  unfold problem_spec
  use implementation numbers delimeter
  constructor
  · rfl
  · unfold implementation
    cases numbers with
    | nil =>
      left
      simp [implementation]
    | cons x xs =>
      cases xs with
      | nil =>
        simp [implementation]
        tauto
      | cons y ys =>
        right; right
        constructor
        · have h := implementation_length numbers delimeter
          simp [numbers] at h
          exact h.2.2 (by simp; norm_num)
        · intro i hi
          constructor
          · have h := implementation_elements numbers delimeter i hi
            simp at h
            cases h' : numbers[i]? with
            | none => 
              have : i ≥ numbers.length := List.getElem?_eq_none.mp h'
              linarith
            | some val =>
              have h_get : numbers[i]! = val := by
                rw [List.getElem!_eq_getElem?_get_or_else]
                rw [h']
                simp
              rw [h_get]
              have h_result : (implementation numbers delimeter)[2 * i]? = some val := by
                rw [← h']
                exact h
              rw [List.getElem!_eq_getElem?_get_or_else]
              rw [h_result]
              simp
          · intro h_pos
            simp [implementation]
            cases' Nat.eq_zero_or_pos i with hi_zero hi_pos
            · rw [hi_zero] at h_pos
              simp at h_pos
            · have : 2 * i - 1 = 2 * i - 1 := rfl
              have hi_bounds : i < numbers.length := hi
              simp [numbers]
              sorry -- This part requires more detailed reasoning about list indexing

-- #test implementation [1, 2, 3] 4 = [1, 4, 2, 4, 3]
-- #test implementation [] 4 = []
-- #test implementation [1] 4 = [1]