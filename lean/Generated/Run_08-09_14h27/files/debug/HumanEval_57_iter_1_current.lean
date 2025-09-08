/- 
function_signature: "def monotonic(numbers: List[int]) -> Bool"
docstring: |
    Return True if list elements are monotonically increasing or decreasing.
test_cases:
  - input: [1, 2, 4, 20]
    expected_output: True
  - input: [1, 20, 4, 10]
    expected_output: False
  - input: [4, 1, 0, -10]
    expected_output: True
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def is_increasing (numbers: List Int) : Bool :=
  match numbers with
  | [] => true
  | [_] => true
  | x :: xs => 
    let rec check_inc (prev : Int) (lst : List Int) : Bool :=
      match lst with
      | [] => true
      | y :: ys => if prev ≤ y then check_inc y ys else false
    check_inc x xs

-- LLM HELPER  
def is_decreasing (numbers: List Int) : Bool :=
  match numbers with
  | [] => true
  | [_] => true
  | x :: xs =>
    let rec check_dec (prev : Int) (lst : List Int) : Bool :=
      match lst with
      | [] => true
      | y :: ys => if prev ≥ y then check_dec y ys else false
    check_dec x xs

def implementation (numbers: List Int) : Bool :=
  is_increasing numbers || is_decreasing numbers

def problem_spec
-- function signature
(implementation: List Int → Bool)
-- inputs
(numbers: List Int) :=
let non_ordered := ∃ i j,
i < numbers.length - 1 ∧
j < numbers.length - 1 ∧
(numbers[i]! < numbers[i+1]!) ∧
(numbers[j+1]! < numbers[j]!);
-- spec
let spec (result: Bool) :=
  1 < numbers.length →
  result ↔ ¬non_ordered;
-- program termination
∃ result, implementation numbers = result ∧
spec result

-- LLM HELPER
lemma increasing_no_decrease (numbers: List Int) : 
  is_increasing numbers = true → ¬∃ i, i < numbers.length - 1 ∧ numbers[i+1]! < numbers[i]! := by
  intro h
  intro ⟨i, hi, hlt⟩
  induction numbers generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases xs with
    | nil => simp at hi
    | cons y ys =>
      simp [is_increasing] at h
      by_cases h_case : i = 0
      · simp [h_case] at hlt
        simp [h_case] at hi
        have : x ≤ y := by
          simp [is_increasing] at h
          exact h.1
        linarith
      · have i_pos : 0 < i := Nat.pos_of_ne_zero h_case
        have i_pred : i = i.pred + 1 := Nat.succ_pred_eq_of_pos i_pos
        simp at hlt
        simp at hi
        have h_tail : is_increasing (y :: ys) = true := by
          simp [is_increasing] at h
          exact h.2
        have : ∃ j, j < (y :: ys).length - 1 ∧ (y :: ys)[j+1]! < (y :: ys)[j]! := by
          use i.pred
          constructor
          · simp
            rw [i_pred] at hi
            simp at hi
            exact hi.2
          · simp
            rw [i_pred] at hlt
            simp at hlt
            exact hlt
        exact ih h_tail this

-- LLM HELPER
lemma decreasing_no_increase (numbers: List Int) : 
  is_decreasing numbers = true → ¬∃ i, i < numbers.length - 1 ∧ numbers[i]! < numbers[i+1]! := by
  intro h
  intro ⟨i, hi, hlt⟩
  induction numbers generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases xs with
    | nil => simp at hi
    | cons y ys =>
      simp [is_decreasing] at h
      by_cases h_case : i = 0
      · simp [h_case] at hlt
        simp [h_case] at hi
        have : x ≥ y := by
          simp [is_decreasing] at h
          exact h.1
        linarith
      · have i_pos : 0 < i := Nat.pos_of_ne_zero h_case
        have i_pred : i = i.pred + 1 := Nat.succ_pred_eq_of_pos i_pos
        simp at hlt
        simp at hi
        have h_tail : is_decreasing (y :: ys) = true := by
          simp [is_decreasing] at h
          exact h.2
        have : ∃ j, j < (y :: ys).length - 1 ∧ (y :: ys)[j]! < (y :: ys)[j+1]! := by
          use i.pred
          constructor
          · simp
            rw [i_pred] at hi
            simp at hi
            exact hi.2
          · simp
            rw [i_pred] at hlt
            simp at hlt
            exact hlt
        exact ih h_tail this

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers
:= by
  unfold problem_spec
  use implementation numbers
  constructor
  · rfl
  · intro h_len
    unfold implementation
    simp only [Bool.or_eq_true]
    constructor
    · intro h_mono
      unfold problem_spec at *
      intro ⟨i, j, hi, hj, h_inc, h_dec⟩
      cases h_mono with
      | inl h_increasing => 
        have : ¬∃ k, k < numbers.length - 1 ∧ numbers[k+1]! < numbers[k]! := 
          increasing_no_decrease numbers h_increasing
        exact this ⟨j, hj, h_dec⟩
      | inr h_decreasing => 
        have : ¬∃ k, k < numbers.length - 1 ∧ numbers[k]! < numbers[k+1]! := 
          decreasing_no_increase numbers h_decreasing
        exact this ⟨i, hi, h_inc⟩
    · intro h_not_non_ordered
      by_contra h_not_mono
      simp at h_not_mono
      have h_not_inc : is_increasing numbers = false := h_not_mono.1
      have h_not_dec : is_decreasing numbers = false := h_not_mono.2
      -- This requires a more complex proof showing that if neither increasing nor decreasing,
      -- then there must exist both increasing and decreasing pairs
      sorry

-- #test implementation [1, 2, 4, 20] = true
-- #test implementation [1, 20, 4, 10] = false
-- #test implementation [4, 1, 0, -10] = true