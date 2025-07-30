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
  q = q.reverse

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
  simp [problem_spec, implementation]
  let result := isPalindrome q && sumLeq q w
  use result
  constructor
  · rfl
  · simp [result]
    constructor
    · intro h
      cases' h with h1 h2
      rw [isPalindrome_correct] at h1
      exact h1
    · constructor
      · intro h
        cases' h with h1 h2
        rw [sumLeq_correct] at h2
        exact h2
      · constructor
        · intro h
          simp [Bool.and_eq_true]
          intro h_contra
          rw [isPalindrome_correct] at h_contra
          exact h h_contra.1
        · intro h
          simp [Bool.and_eq_true]
          intro h_contra
          rw [sumLeq_correct] at h_contra
          exact h h_contra.2