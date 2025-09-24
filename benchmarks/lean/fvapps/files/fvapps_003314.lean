-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def correct_polish_letters (s : String) : String := sorry

theorem length_preserved (s : String) :
  (correct_polish_letters s).length = s.length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem non_polish_chars_unchanged (s : String) (i : Nat) (h : i < s.length) :
  s.data[i] ∉ ['ą', 'ć', 'ę', 'ł', 'ń', 'ó', 'ś', 'ź', 'ż'] →
  have h' : i < (correct_polish_letters s).length := by rw [length_preserved]; exact h
  (correct_polish_letters s).data[i] = s.data[i] := sorry

theorem polish_chars_translated_correctly (s : String) (i : Nat) (h : i < s.length) :
  have h' : i < (correct_polish_letters s).length := by rw [length_preserved]; exact h
  s.data[i] = 'ą' → (correct_polish_letters s).data[i] = 'a' ∧
  s.data[i] = 'ć' → (correct_polish_letters s).data[i] = 'c' ∧
  s.data[i] = 'ę' → (correct_polish_letters s).data[i] = 'e' ∧
  s.data[i] = 'ł' → (correct_polish_letters s).data[i] = 'l' ∧
  s.data[i] = 'ń' → (correct_polish_letters s).data[i] = 'n' ∧
  s.data[i] = 'ó' → (correct_polish_letters s).data[i] = 'o' ∧
  s.data[i] = 'ś' → (correct_polish_letters s).data[i] = 's' ∧
  s.data[i] = 'ź' → (correct_polish_letters s).data[i] = 'z' ∧
  s.data[i] = 'ż' → (correct_polish_letters s).data[i] = 'z' := sorry

theorem idempotent (s : String) :
  correct_polish_letters (correct_polish_letters s) = correct_polish_letters s := sorry
-- </vc-theorems>