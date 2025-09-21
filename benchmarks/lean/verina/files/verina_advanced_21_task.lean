-- <vc-preamble>
@[reducible, simp]
def isPalindrome_precond (s : String) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isPalindrome (s : String) (h_precond : isPalindrome_precond (s)) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def isPalindrome_postcond (s : String) (result: Bool) (h_precond : isPalindrome_precond (s)) : Prop :=
  (result → (s.toList == s.toList.reverse)) ∧
  (¬ result → (s.toList ≠ [] ∧ s.toList != s.toList.reverse))

theorem isPalindrome_spec_satisfied (s: String) (h_precond : isPalindrome_precond (s)) :
    isPalindrome_postcond (s) (isPalindrome (s) h_precond) h_precond := by
  sorry
-- </vc-theorems>