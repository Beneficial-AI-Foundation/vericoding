import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Nat.Basic
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
def isPalindrome (q: List Int) : Bool :=
  q.reverse = q

-- LLM HELPER
def sumLeq (q: List Int) (w: Int) : Bool :=
  List.sum q ≤ w

def implementation (q: List Int) (w: Int) : Bool := 
  isPalindrome q && sumLeq q w

-- LLM HELPER
lemma isPalindrome_correct (q: List Int) : isPalindrome q = true ↔ List.Palindrome q := by
  simp [isPalindrome, List.Palindrome]

-- LLM HELPER
lemma sumLeq_correct (q: List Int) (w: Int) : sumLeq q w = true ↔ List.sum q ≤ w := by
  simp [sumLeq]

theorem correctness
(q: List Int) (w: Int)
: problem_spec implementation q w := by
  unfold problem_spec
  use implementation q w
  constructor
  · rfl
  · unfold implementation
    simp [isPalindrome_correct, sumLeq_correct]
    constructor
    · intro h
      cases h with
      | mk h1 h2 => exact h1
    · constructor
      · intro h
        cases h with
        | mk h1 h2 => exact h2
      · constructor
        · intro h1 h2
          simp at h2
          cases h2 with
          | inl h => exact h1 h
          | inr h => contradiction
        · intro h1 h2
          simp at h2
          cases h2 with
          | inl h => contradiction
          | inr h => exact h1 h