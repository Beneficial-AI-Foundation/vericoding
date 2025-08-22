import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
(implementation: List Int → Int → Bool)
(q: List Int) (w: Int) :=
let spec (result : Bool) :=
  (result → (List.Palindrome q)) ∧
  (result → (List.sum q ≤ w)) ∧
  (¬(List.Palindrome q) → ¬ result) ∧
  (¬(List.sum q ≤ w) → ¬ result)
∃ result, implementation q w = result ∧
spec result

-- LLM HELPER
def decidable_palindrome (q : List Int) : Bool :=
  q = q.reverse

-- LLM HELPER
def decidable_sum_le (q : List Int) (w : Int) : Bool :=
  q.sum ≤ w

def implementation (q: List Int) (w: Int) : Bool := 
  decidable_palindrome q && decidable_sum_le q w

-- LLM HELPER
theorem decidable_palindrome_correct (q : List Int) :
  decidable_palindrome q = true ↔ List.Palindrome q := by
  simp [decidable_palindrome]
  constructor
  · intro h
    rw [List.palindrome_iff_reverse]
    exact h
  · intro h
    rw [← List.palindrome_iff_reverse] at h
    exact h

-- LLM HELPER
theorem decidable_sum_le_correct (q : List Int) (w : Int) :
  decidable_sum_le q w = true ↔ q.sum ≤ w := by
  simp [decidable_sum_le]

theorem correctness
(q: List Int) (w: Int)
: problem_spec implementation q w := by
  simp [problem_spec]
  use (decidable_palindrome q && decidable_sum_le q w)
  constructor
  · simp [implementation]
  · simp [implementation]
    constructor
    · intro h
      simp [Bool.and_eq_true] at h
      have h1 := h.1
      rw [← decidable_palindrome_correct] at h1
      exact h1
    · constructor
      · intro h
        simp [Bool.and_eq_true] at h
        have h2 := h.2
        rw [← decidable_sum_le_correct] at h2
        exact h2
      · constructor
        · intro h
          simp [Bool.and_eq_true]
          push_neg
          left
          rw [decidable_palindrome_correct]
          exact h
        · intro h
          simp [Bool.and_eq_true]
          push_neg
          right
          rw [decidable_sum_le_correct]
          exact h