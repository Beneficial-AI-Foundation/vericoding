-- <vc-helpers>
-- </vc-helpers>

def isAlpha (c : Char) : Bool := sorry
def reverseOnlyLetters (s : String) : String := sorry

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

/-
info: 'dc-ba'
-/
-- #guard_msgs in
-- #eval reverse_only_letters "ab-cd"

/-
info: 'j-Ih-gfE-dCba'
-/
-- #guard_msgs in
-- #eval reverse_only_letters "a-bC-dEf-ghIj"

/-
info: 'Qedo1ct-eeLg=ntse-T!'
-/
-- #guard_msgs in
-- #eval reverse_only_letters "Test1ng-Leet=code-Q!"

-- Apps difficulty: introductory
-- Assurance level: unguarded