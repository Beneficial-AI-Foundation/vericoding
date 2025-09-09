-- <vc-helpers>
-- </vc-helpers>

def solve (pattern text : String) : Nat := sorry

theorem pattern_in_text : ∀ (pattern : String) (extra : String), 
  pattern.length > 0 → solve pattern (pattern ++ extra) ≥ 1 := sorry

theorem single_char_pattern : ∀ (c : Char) (text : String),
  solve (String.mk [c]) text = (text.data.filter (· = c)).length := sorry

theorem empty_text : ∀ (pattern : String),
  pattern.length > 1 → solve pattern "" = 0 := sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval solve "zaz" "zazapulz"

/-
info: 3
-/
-- #guard_msgs in
-- #eval solve "rat" "ratatoulie"

/-
info: 7
-/
-- #guard_msgs in
-- #eval solve "kata" "katakatak"

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible