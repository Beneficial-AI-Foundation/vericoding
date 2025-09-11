-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def longest (s : String) : String := sorry

theorem longest_is_substring (s : String) :
  ∃ i j, s.extract i j = longest s := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem longest_is_ordered (s : String) :
  let result := longest s
  ∀ (i j : String.Pos), i < j → result.get i ≤ result.get j := sorry

theorem longest_length_bounded (s : String) :
  (longest s).length ≤ s.length := sorry

theorem nonempty_input_nonempty_output (s : String) (h : s.length > 0) :
  (longest s).length > 0 := sorry

/-
info: 'as'
-/
-- #guard_msgs in
-- #eval longest "asd"

/-
info: 'abcde'
-/
-- #guard_msgs in
-- #eval longest "abcdeapbcdef"

/-
info: 'aaaabbbbctt'
-/
-- #guard_msgs in
-- #eval longest "asdfaaaabbbbcttavvfffffdf"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded