-- <vc-helpers>
-- </vc-helpers>

def double_check (s : String) : Bool := sorry

theorem double_check_returns_bool (s : String) :
  double_check s = true ∨ double_check s = false := sorry

theorem double_check_repeating_chars {s : String} 
  (h : ∃ (c : Char) (i j : String.Pos), i < j ∧ 
    s.get i = c ∧ s.get j = c) :
  double_check s = true := sorry

theorem double_check_case_insensitive {s : String}
  (h : s.length ≥ 2) :
  ∃ i j : String.Pos, i < j → double_check s = true := sorry

theorem double_check_single_char {s : String}
  (h : s.length = 1) :
  double_check s = false := sorry

/-
info: False
-/
-- #guard_msgs in
-- #eval double_check "abca"

/-
info: True
-/
-- #guard_msgs in
-- #eval double_check "aabc"

/-
info: True
-/
-- #guard_msgs in
-- #eval double_check "a 11 c d"

-- Apps difficulty: introductory
-- Assurance level: unguarded