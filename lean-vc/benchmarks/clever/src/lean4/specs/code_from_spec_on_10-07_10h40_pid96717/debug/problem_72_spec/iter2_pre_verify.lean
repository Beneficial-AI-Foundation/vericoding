import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def List.Palindrome (l : List α) : Bool :=
  l = l.reverse

-- LLM HELPER
def List.sum (l : List Int) : Int :=
  l.foldl (· + ·) 0

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

def implementation (q: List Int) (w: Int) : Bool := 
  List.Palindrome q ∧ List.sum q ≤ w

theorem correctness
(q: List Int) (w: Int)
: problem_spec implementation q w := by
  unfold problem_spec
  use List.Palindrome q ∧ List.sum q ≤ w
  constructor
  · rfl
  · simp only [and_imp]
    constructor
    · intro h
      exact h.1
    constructor
    · intro h
      exact h.2
    constructor
    · intro h_not_pal h_result
      exact h_not_pal h_result.1
    · intro h_not_sum h_result
      exact h_not_sum h_result.2