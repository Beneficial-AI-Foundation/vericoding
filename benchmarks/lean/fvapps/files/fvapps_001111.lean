-- <vc-preamble>
def mkPos (s : String) (i : Nat) (h : i < s.length) : String.Pos := ⟨i⟩
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isPalindrome (s : String) : Bool :=
sorry

def countPalindromeCompletions (s : String) : Nat :=
sorry

def reverseString (s : String) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem countPalindromeCompletions_nonnegative (s : String) :
  countPalindromeCompletions s ≥ 0 :=
sorry

theorem countPalindromeCompletions_impossible_case (s : String) (i : Nat)
  (h1 : i < s.length / 2)
  (h2 : i < s.length)
  (h3 : s.length - 1 - i < s.length)
  (h4 : s.get (mkPos s i h2) ≠ '?' ∧ s.get (mkPos s (s.length - 1 - i) h3) ≠ '?')
  (h5 : s.get (mkPos s i h2) ≠ s.get (mkPos s (s.length - 1 - i) h3)) :
  countPalindromeCompletions s = 0 :=
sorry

theorem countPalindromeCompletions_bounded (s : String) :
  countPalindromeCompletions s ≤ 10000009 :=
sorry

theorem countPalindromeCompletions_all_question_marks (s : String) (h : ∀ c ∈ s.data, c = '?') :
  countPalindromeCompletions s = (26 ^ ((s.length + 1) / 2)) % 10000009 :=
sorry

theorem countPalindromeCompletions_no_question_marks (s : String) (h : '?' ∉ s.data) :
  countPalindromeCompletions s = if isPalindrome s then 1 else 0 :=
sorry

theorem countPalindromeCompletions_deterministic (s : String) :
  countPalindromeCompletions s = countPalindromeCompletions s :=
sorry

theorem countPalindromeCompletions_symmetry (s : String) :
  countPalindromeCompletions s = countPalindromeCompletions (reverseString s) :=
sorry
-- </vc-theorems>