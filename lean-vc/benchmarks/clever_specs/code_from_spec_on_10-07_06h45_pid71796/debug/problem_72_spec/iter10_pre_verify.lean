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
def List.Palindrome (l : List α) : Prop := l = l.reverse

-- LLM HELPER
def isPalindrome (q: List Int) : Bool :=
  q == q.reverse

def implementation (q: List Int) (w: Int) : Bool := 
  isPalindrome q && (q.sum ≤ w)

-- LLM HELPER
lemma isPalindrome_correct (q: List Int) : isPalindrome q = true ↔ List.Palindrome q := by
  simp [isPalindrome, List.Palindrome]
  rfl

-- LLM HELPER
lemma bool_and_true_iff (a b : Bool) : (a && b) = true ↔ a = true ∧ b = true := by
  simp [Bool.and_eq_true]

-- LLM HELPER
lemma decidable_le_bool (a b : Int) : (a ≤ b) ↔ (a ≤ b) = true := by
  simp

theorem correctness
(q: List Int) (w: Int)
: problem_spec implementation q w := by
  unfold problem_spec
  use implementation q w
  constructor
  · rfl
  · unfold implementation
    simp [bool_and_true_iff, isPalindrome_correct]
    constructor
    · intro h
      exact h.1
    · constructor
      · intro h
        exact h.2
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