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
          have : (y :: ys).length ≥ 1 := by simp
          cases ys with
          | nil => simp
          | cons z zs => simp at h1
        rw [h_eq] at ih
        have ih_prop := ih.2.1
        simp at ih_prop
        simp [h_eq]
        norm_num
      · have ih_ge2 := ih.2.2 h2
        simp only [List.length_cons] at ih_ge2 ⊢
        rw [ih_ge2]
        ring

-- LLM HELPER
lemma implementation_correct_structure (numbers: List Int) (delimeter: Int) :
  match numbers with
  | [] => implementation numbers delimeter = []
  | [x] => implementation numbers delimeter = [x]
  | x :: xs => implementation numbers delimeter = x :: delimeter :: implementation xs delimeter :=
by
  cases numbers with
  | nil => simp [implementation]
  | cons x xs =>
    cases xs with
    | nil => simp [implementation]
    | cons y ys => simp [implementation]

theorem correctness
(numbers: List Int)
(delimeter: Int)
: problem_spec implementation numbers delimeter
:= by
  unfold problem_spec
  use implementation numbers delimeter
  constructor
  · rfl
  · cases numbers with
    | nil =>
      left
      simp [implementation]
    | cons x xs =>
      cases xs with
      | nil =>
        right; left
        simp [implementation]
      | cons y ys =>
        right; right
        constructor
        · have h := implementation_length (x :: y :: ys) delimeter
          simp at h
          exact h.2.2 (by simp; norm_num)
        · intro i hi
          constructor
          · -- Show result[2*i]! = numbers[i]!
            induction i generalizing x y ys with
            | zero => 
              simp [implementation]
            | succ j ih_j =>
              simp [implementation]
              have hj : j < (y :: ys).length := by simp at hi; exact Nat.lt_of_succ_lt_succ hi
              cases' (y :: ys) with z zs
              · simp at hj
              · have := ih_j y z zs hj
                simp [implementation] at this
                exact this
          · -- Show 0 < 2*i - 1 → result[2*i - 1]! = delimeter
            intro h_pos
            induction i generalizing x y ys with
            | zero => simp at h_pos
            | succ j ih_j =>
              have hj : j < (y :: ys).length := by simp at hi; exact Nat.lt_of_succ_lt_succ hi
              cases' (y :: ys) with z zs
              · simp at hj
              · simp [implementation]
                cases j with
                | zero => simp
                | succ k =>
                  have hk : k < zs.length := by simp at hj; exact Nat.lt_of_succ_lt_succ hj
                  cases' zs with w ws
                  · simp at hk
                  · have := ih_j z w ws hk
                    simp [implementation] at this
                    exact this (by omega)

-- #test implementation [1, 2, 3] 4 = [1, 4, 2, 4, 3]
-- #test implementation [] 4 = []
-- #test implementation [1] 4 = [1]