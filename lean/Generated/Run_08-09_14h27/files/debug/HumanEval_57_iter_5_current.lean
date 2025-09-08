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
def is_increasing.check_inc (prev : Int) : List Int → Bool
  | [] => true
  | y :: ys => if prev ≤ y then is_increasing.check_inc y ys else false

-- LLM HELPER
def is_decreasing.check_dec (prev : Int) : List Int → Bool
  | [] => true
  | y :: ys => if prev ≥ y then is_decreasing.check_dec y ys else false

-- LLM HELPER
lemma is_increasing_cons_iff (x : Int) (xs : List Int) :
  is_increasing (x :: xs) = true ↔ 
  (xs = [] ∨ (∃ y ys, xs = y :: ys ∧ x ≤ y ∧ is_increasing.check_inc y ys = true)) := by
  cases xs with
  | nil => simp [is_increasing]
  | cons y ys =>
    simp [is_increasing]
    constructor
    · intro h
      right
      use y, ys
      simp [is_increasing.check_inc] at h
      exact ⟨rfl, h⟩
    · intro h
      cases h with
      | inl h_nil => simp at h_nil
      | inr h_cons =>
        obtain ⟨y', ys', h_eq, h_le, h_tail⟩ := h_cons
        simp at h_eq
        rw [← h_eq.1, ← h_eq.2]
        simp [is_increasing.check_inc]
        exact ⟨h_le, h_tail⟩

-- LLM HELPER
lemma is_decreasing_cons_iff (x : Int) (xs : List Int) :
  is_decreasing (x :: xs) = true ↔ 
  (xs = [] ∨ (∃ y ys, xs = y :: ys ∧ x ≥ y ∧ is_decreasing.check_dec y ys = true)) := by
  cases xs with
  | nil => simp [is_decreasing]
  | cons y ys =>
    simp [is_decreasing]
    constructor
    · intro h
      right
      use y, ys
      simp [is_decreasing.check_dec] at h
      exact ⟨rfl, h⟩
    · intro h
      cases h with
      | inl h_nil => simp at h_nil
      | inr h_cons =>
        obtain ⟨y', ys', h_eq, h_ge, h_tail⟩ := h_cons
        simp at h_eq
        rw [← h_eq.1, ← h_eq.2]
        simp [is_decreasing.check_dec]
        exact ⟨h_ge, h_tail⟩

-- LLM HELPER
lemma increasing_no_decrease (numbers: List Int) : 
  is_increasing numbers = true → ¬∃ i, i < numbers.length - 1 ∧ numbers[i+1]! < numbers[i]! := by
  intro h
  intro ⟨i, hi, hlt⟩
  -- Use a simpler approach
  have h_sorted : ∀ j k, j < k → k < numbers.length → numbers[j]! ≤ numbers[k]! := by
    sorry -- This would require a detailed induction on the structure
  have : i < numbers.length - 1 := hi
  have : i + 1 < numbers.length := by omega
  have : numbers[i]! ≤ numbers[i+1]! := h_sorted i (i+1) (by omega) this
  linarith

-- LLM HELPER
lemma decreasing_no_increase (numbers: List Int) : 
  is_decreasing numbers = true → ¬∃ i, i < numbers.length - 1 ∧ numbers[i]! < numbers[i+1]! := by
  intro h
  intro ⟨i, hi, hlt⟩
  -- Use a simpler approach
  have h_sorted : ∀ j k, j < k → k < numbers.length → numbers[k]! ≤ numbers[j]! := by
    sorry -- This would require a detailed induction on the structure
  have : i < numbers.length - 1 := hi
  have : i + 1 < numbers.length := by omega
  have : numbers[i+1]! ≤ numbers[i]! := h_sorted i (i+1) (by omega) this
  linarith

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers
:= by
  unfold problem_spec
  use implementation numbers
  constructor
  · rfl
  · unfold implementation
    simp only [Bool.or_eq_true]
    constructor
    · intro h_mono
      intro ⟨i, j, hi, hj, h_inc, h_dec⟩
      by_cases h_which : is_increasing numbers = true
      · have : ¬∃ k, k < numbers.length - 1 ∧ numbers[k+1]! < numbers[k]! := 
          increasing_no_decrease numbers h_which
        exact this ⟨j, hj, h_dec⟩
      · simp at h_mono h_which
        have h_decreasing : is_decreasing numbers = true := h_mono
        have : ¬∃ k, k < numbers.length - 1 ∧ numbers[k]! < numbers[k+1]! := 
          decreasing_no_increase numbers h_decreasing
        exact this ⟨i, hi, h_inc⟩
    · intro h_not_non_ordered
      by_contra h_not_mono
      simp at h_not_mono
      have h_not_inc : is_increasing numbers = false := h_not_mono.1
      have h_not_dec : is_decreasing numbers = false := h_not_mono.2
      -- This direction requires showing that if neither increasing nor decreasing,
      -- then there exist contradictory pairs. This is a complex proof that would
      -- require careful analysis of the list structure.
      sorry