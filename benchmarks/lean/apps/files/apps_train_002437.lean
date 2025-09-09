-- <vc-helpers>
-- </vc-helpers>

def find_first_repeated_char (s : String) : String := sorry

theorem find_first_repeated_char_output_type (s : String) :
  let result := find_first_repeated_char s
  result.length = 1 ∨ result = "-1" := sorry

theorem find_first_repeated_char_valid_output (s : String) :
  let result := find_first_repeated_char s 
  result ≠ "-1" →
  (∃ i : Fin s.length, 
    ∃ c : Char, result = String.mk [c] ∧
    s.data[i.val]? = some c ∧
    i.val + 1 < s.length ∧
    s.data[i.val + 1]? = some c) ∧
  ∀ j : Fin s.length, j.val + 1 < s.length →
    s.data[j.val]? = s.data[j.val + 1]? →
    ∃ m : Fin s.length, m.val ≤ j.val ∧ 
    s.data[m.val]? = s.data[m.val + 1]? := sorry

theorem find_first_repeated_char_alphanumeric (s : String) :
  (∀ i : Fin s.length, (s.data[i.val]?).map Char.isAlphanum = some true) →
  s.length ≥ 2 →
  let result := find_first_repeated_char s
  result ≠ "-1" →
  (result.data[0]?).map Char.isAlphanum = some true := sorry

theorem find_first_repeated_char_with_repeats (s : String) :
  (∃ (i : Fin s.length), i.val + 1 < s.length ∧ s.data[i.val]? = s.data[i.val + 1]?) →
  find_first_repeated_char s ≠ "-1" := sorry

/-
info: '1'
-/
-- #guard_msgs in
-- #eval find_first_repeated_char "12345678910111213141516171820212223"

/-
info: '-1'
-/
-- #guard_msgs in
-- #eval find_first_repeated_char "abcde"

/-
info: 'a'
-/
-- #guard_msgs in
-- #eval find_first_repeated_char "aabbccdd"

-- Apps difficulty: introductory
-- Assurance level: unguarded