/- 
function_signature: "def will_it_fly(q: List[int], w: int) -> bool"
docstring: |
    Write a function that returns True if the object q will fly, and False otherwise.
    The object q will fly if it's balanced (it is a palindromic list) and the sum of its elements is
    less than or equal the maximum possible weight w.
test_cases:
  - input: ([1, 2], 5)
    expected_output: False
  - input: ([3, 2, 3], 1)
    expected_output: False
  - input: ([3, 2, 3], 9)
    expected_output: True
  - input: ([3], 5)
    expected_output: True
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def is_palindrome (q: List Int) : Bool :=
  q = q.reverse

def implementation (q: List Int) (w: Int) : Bool :=
  is_palindrome q && List.sum q ≤ w

def problem_spec
-- function signature
(implementation: List Int → Int → Bool)
-- inputs
(q: List Int) (w: Int) :=
-- spec
let spec (result : Bool) :=
  (result → (List.Palindrome q)) ∧
  (result → (List.sum q ≤ w)) ∧
  (¬(List.Palindrome q) → ¬ result) ∧
  (¬(List.sum q ≤ w) → ¬ result)
-- program termination
∃ result, implementation q w = result ∧
spec result

-- LLM HELPER
lemma is_palindrome_iff_palindrome (q: List ℤ) : 
  q = q.reverse ↔ q.Palindrome := List.palindrome_iff_eq_reverse.symm

-- LLM HELPER  
lemma implementation_true_iff (q: List Int) (w: Int) :
  implementation q w = true ↔ (List.Palindrome q ∧ List.sum q ≤ w) := by
  simp [implementation]
  constructor
  · intro ⟨h1, h2⟩
    constructor
    · rw [← is_palindrome_iff_palindrome]
      exact h1
    · exact h2
  · intro ⟨h1, h2⟩
    constructor
    · rw [is_palindrome_iff_palindrome]
      exact h1
    · exact h2

-- LLM HELPER
lemma implementation_false_iff (q: List Int) (w: Int) :
  implementation q w = false ↔ (¬List.Palindrome q ∨ ¬(List.sum q ≤ w)) := by
  simp [implementation]
  simp [Bool.and_eq_false_iff]
  constructor
  · intro h
    cases h with
    | inl h1 => 
      left
      rw [← is_palindrome_iff_palindrome] at h1
      exact h1
    | inr h2 =>
      right
      exact h2
  · intro h
    cases h with
    | inl h1 =>
      left
      rw [is_palindrome_iff_palindrome]
      exact h1
    | inr h2 =>
      right
      exact h2

theorem correctness
(q: List Int) (w: Int)
: problem_spec implementation q w
:= by
  use implementation q w
  constructor
  · rfl
  · simp only []
    by_cases h1 : List.Palindrome q
    · by_cases h2 : List.sum q ≤ w
      · -- Both conditions true, result should be true
        have result_true : implementation q w = true := by
          rw [implementation_true_iff]
          exact ⟨h1, h2⟩
        rw [result_true]
        simp [h1, h2]
      · -- Palindrome but sum too large, result should be false
        have result_false : implementation q w = false := by
          rw [implementation_false_iff]
          right
          exact h2
        rw [result_false]
        simp [h1, h2]
    · -- Not palindrome, result should be false
      have result_false : implementation q w = false := by
        rw [implementation_false_iff]
        left
        exact h1
      rw [result_false]
      simp [h1]