def is_valid_encoding (s : String) : Bool :=
  sorry

def count_decodings (s : String) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def num_decodings (s : String) : Nat :=
  sorry

theorem valid_strings (s : String) :
  is_valid_encoding s → num_decodings s = count_decodings s :=
  sorry

theorem invalid_strings (s : String) :
  ¬is_valid_encoding s → num_decodings s = 0 :=
  sorry

theorem empty_string :
  num_decodings "" = 0 :=
  sorry

theorem starting_zero (s : String) :
  s.length > 0 → s.front = '0' → num_decodings s = 0 :=
  sorry

theorem short_valid_numbers (s : String) :
  is_valid_encoding s → s.length ≤ 6 → num_decodings s = count_decodings s :=
  sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval num_decodings "12"

/-
info: 3
-/
-- #guard_msgs in
-- #eval num_decodings "226"

/-
info: 0
-/
-- #guard_msgs in
-- #eval num_decodings "06"

-- Apps difficulty: interview
-- Assurance level: unguarded