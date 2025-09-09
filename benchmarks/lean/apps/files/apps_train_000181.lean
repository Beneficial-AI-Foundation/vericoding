-- <vc-helpers>
-- </vc-helpers>

def max_repeated_chars_with_swap (s : String) : Nat :=
  sorry

theorem single_char_string_property (s : String) (h : s.length > 0)
  (h_single : (s.data.eraseDups).length = 1) :
  max_repeated_chars_with_swap s = s.length :=
  sorry

theorem result_bounds (s : String) (h : s.length > 0) :
  1 ≤ max_repeated_chars_with_swap s ∧ max_repeated_chars_with_swap s ≤ s.length :=
  sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval max_repeated_chars_with_swap "ababa"

/-
info: 6
-/
-- #guard_msgs in
-- #eval max_repeated_chars_with_swap "aaabaaa"

/-
info: 4
-/
-- #guard_msgs in
-- #eval max_repeated_chars_with_swap "aaabbaaa"

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible