def find_largest_sequence (s : String) : Nat :=
  sorry

def isSubstring (sub str : String) : Bool :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def substring (s : String) (start len : Nat) : String :=
  sorry

theorem short_strings (s : String) :
  s.length < 5 → find_largest_sequence s = 0 :=
sorry

/-
info: 98765
-/
-- #guard_msgs in
-- #eval find_largest_sequence "1234567898765"

/-
info: 67890
-/
-- #guard_msgs in
-- #eval find_largest_sequence "1234567890"

/-
info: 12345
-/
-- #guard_msgs in
-- #eval find_largest_sequence "12345"

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible