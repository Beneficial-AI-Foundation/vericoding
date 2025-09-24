-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isAlpha (c : Char) : Bool := sorry
def reverseOnlyLetters (s : String) : String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem length_preservation (s : String) :
  (reverseOnlyLetters s).length = s.length := sorry

theorem non_letters_unchanged (s : String) (i : String.Pos) :
  ¬(isAlpha (s.get i)) → (reverseOnlyLetters s).get i = s.get i := sorry

theorem letter_count_preserved (s : String) :
  (s.data.filter isAlpha).length = ((reverseOnlyLetters s).data.filter isAlpha).length := sorry

theorem double_reverse_identity (s : String) :
  reverseOnlyLetters (reverseOnlyLetters s) = s := sorry

theorem all_letters_simple_reverse (s : String) :
  (∀ c ∈ s.data, isAlpha c) → reverseOnlyLetters s = String.mk s.data.reverse := sorry

theorem no_letters_unchanged (s : String) :
  (∀ c ∈ s.data, ¬(isAlpha c)) → reverseOnlyLetters s = s := sorry
-- </vc-theorems>