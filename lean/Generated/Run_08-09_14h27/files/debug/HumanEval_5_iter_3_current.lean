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

def implementation (numbers: List Int) (delimiter: Int) : List Int :=
  match numbers with
  | [] => []
  | [x] => [x]
  | x :: xs => x :: delimiter :: implementation xs delimiter

def problem_spec
-- function signature
(implementation: List Int → Int → List Int)
-- inputs
(numbers: List Int)
(delimiter: Int) :=
-- spec
let spec (result: List Int) :=
(result.length = 0 ∧ result = numbers) ∨
(result.length = 1 ∧ numbers.length = 1 ∧
result[0]! = numbers[0]!) ∨
(result.length = 2 * numbers.length - 1 ∧ numbers.length ≥ 2 ∧
∀ i, i < numbers.length →
result[2 * i]! = numbers[i]! ∧
(2*i + 1 < result.length → result[2 * i + 1]! = delimiter));
-- program termination
∃ result, implementation numbers delimiter = result ∧
spec result

-- LLM HELPER
lemma implementation_empty (delimiter : Int) : implementation [] delimiter = [] := by simp [implementation]

-- LLM HELPER
lemma implementation_single (x : Int) (delimiter : Int) : implementation [x] delimiter = [x] := by simp [implementation]

-- LLM HELPER
lemma implementation_length (numbers : List Int) (delimiter : Int) :
  numbers.length ≥ 2 → (implementation numbers delimiter).length = 2 * numbers.length - 1 := by
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
        simp at ih_applied
        simp [ih_applied]
        omega
      | inr h2 =>
        simp at h2
        cases ys with
        | nil => simp [implementation]; omega
        | cons z zs => simp at h2

-- LLM HELPER
lemma implementation_get_even (numbers : List Int) (delimiter : Int) (i : Nat) :
  i < numbers.length → numbers.length ≥ 2 → (implementation numbers delimiter)[2 * i]! = numbers[i]! := by
  intro h h_len
  induction numbers generalizing i with
  | nil => simp at h
  | cons x xs ih =>
    cases i with
    | zero =>
      cases xs with
      | nil => simp at h_len
      | cons y ys => simp [implementation]
    | succ i' =>
      cases xs with
      | nil => simp at h
      | cons y ys =>
        simp [implementation]
        simp at h
        have h' : i' < (y :: ys).length := Nat.lt_of_succ_lt_succ h
        have h_len' : (y :: ys).length ≥ 2 := by simp; omega
        have ih_result := ih h_len' h'
        exact ih_result

-- LLM HELPER
lemma implementation_get_odd (numbers : List Int) (delimiter : Int) (i : Nat) :
  i < numbers.length → numbers.length ≥ 2 → 2*i + 1 < (implementation numbers delimiter).length → 
  (implementation numbers delimiter)[2 * i + 1]! = delimiter := by
  intro h h_len h_bound
  induction numbers generalizing i with
  | nil => simp at h
  | cons x xs ih =>
    cases i with
    | zero =>
      cases xs with
      | nil => simp at h_len
      | cons y ys => simp [implementation]
    | succ i' =>
      cases xs with
      | nil => simp at h
      | cons y ys =>
        simp [implementation]
        simp at h
        have h' : i' < (y :: ys).length := Nat.lt_of_succ_lt_succ h
        have h_len' : (y :: ys).length ≥ 2 := by simp; omega
        have h_bound' : 2 * i' + 1 < (implementation (y :: ys) delimiter).length := by
          simp at h_bound
          omega
        exact ih h_len' h' h_bound'

theorem correctness
(numbers: List Int)
(delimiter: Int)
: problem_spec implementation numbers delimiter
:= by
  unfold problem_spec
  use implementation numbers delimiter
  constructor
  · rfl
  · cases numbers with
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
        · simp [implementation_single]
      | cons y ys =>
        right
        right
        constructor
        · have h : (x :: y :: ys).length ≥ 2 := by simp; omega
          exact implementation_length (x :: y :: ys) delimiter h
        constructor
        · simp; omega
        · intro i h
          constructor
          · have h_len : (x :: y :: ys).length ≥ 2 := by simp; omega
            exact implementation_get_even (x :: y :: ys) delimiter i h h_len
          · intro h_bound
            have h_len : (x :: y :: ys).length ≥ 2 := by simp; omega
            exact implementation_get_odd (x :: y :: ys) delimiter i h h_len h_bound

-- #test implementation [1, 2, 3] 4 = [1, 4, 2, 4, 3]
-- #test implementation [] 4 = []
-- #test implementation [1] 4 = [1]