-- <vc-helpers>
-- </vc-helpers>

def count_segments (s : String) : Nat := sorry

theorem count_segments_empty :
  count_segments "" = 0 := sorry

theorem count_segments_basic_cases :
  count_segments "Hello world" = 2 ∧
  count_segments "   spaces   around   " = 2 := sorry

/-
info: 5
-/
-- #guard_msgs in
-- #eval count_segments "Hello, my name is John"

/-
info: 0
-/
-- #guard_msgs in
-- #eval count_segments ""

/-
info: 1
-/
-- #guard_msgs in
-- #eval count_segments "Hello"

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible