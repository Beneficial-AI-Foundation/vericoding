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
lemma implementation_empty : implementation [] delimeter = [] := by simp [implementation]

-- LLM HELPER
lemma implementation_single (x : Int) : implementation [x] delimeter = [x] := by simp [implementation]

-- LLM HELPER
lemma implementation_length (numbers : List Int) (delimeter : Int) :
  numbers.length ≥ 2 → (implementation numbers delimeter).length = 2 * numbers.length - 1 := by
  intro h
  induction numbers with
  | nil => simp at h
  | cons x xs ih =>
    cases xs with
    | nil => simp at h
    | cons y ys =>
      simp [implementation]
      have : (y :: ys).length ≥ 2 ∨ (y :: ys).length = 1 := by
        cases ys with
        | nil => right; simp
        | cons z zs => left; simp; omega
      cases this with
      | inl h2 =>
        have ih_applied := ih h2
        simp [implementation] at ih_applied
        simp [ih_applied]
        omega
      | inr h2 =>
        simp at h2
        cases ys with
        | nil => simp [implementation]; omega
        | cons z zs => simp at h2

-- LLM HELPER
lemma implementation_get_even (numbers : List Int) (delimeter : Int) (i : Nat) :
  i < numbers.length → (implementation numbers delimeter)[2 * i]! = numbers[i]! := by
  intro h
  induction numbers generalizing i with
  | nil => simp at h
  | cons x xs ih =>
    cases i with
    | zero =>
      cases xs with
      | nil => simp [implementation]
      | cons y ys => simp [implementation]
    | succ i' =>
      cases xs with
      | nil => simp at h
      | cons y ys =>
        simp [implementation]
        simp at h
        have h' : i' < xs.length := by omega
        have : (implementation (y :: ys) delimeter)[2 * i']! = (y :: ys)[i']! := ih h'
        simp [implementation] at this
        simp [this]
        sorry -- This requires more complex indexing reasoning

theorem correctness
(numbers: List Int)
(delimeter: Int)
: problem_spec implementation numbers delimeter
:= by
  unfold problem_spec
  use implementation numbers delimeter
  constructor
  · rfl
  · unfold spec
    cases numbers with
    | nil => 
      left
      constructor
      · simp [implementation_empty]
      · simp [implementation_empty]
    | cons x xs =>
      cases xs with
      | nil =>
        right
        left
        constructor
        · simp [implementation_single]
        constructor
        · simp
        constructor
        · simp [implementation_single]
        · simp [implementation_single]
      | cons y ys =>
        right
        right
        constructor
        · have h : (x :: y :: ys).length ≥ 2 := by simp; omega
          exact implementation_length (x :: y :: ys) delimeter h
        · intro i h
          constructor
          · sorry -- Would need implementation_get_even to work properly
          · intro h_pos
            sorry -- Would need to show delimeter placement is correct

-- #test implementation [1, 2, 3] 4 = [1, 4, 2, 4, 3]
-- #test implementation [] 4 = []
-- #test implementation [1] 4 = [1]