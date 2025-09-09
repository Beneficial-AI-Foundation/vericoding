def count_char (s : String) (c : Char) : Nat := sorry

def take_prefix (s : String) (n : Nat) : String := sorry

-- <vc-helpers>
-- </vc-helpers>

def is_balanced (s : String) (caps : String) : Bool := sorry

theorem single_char_caps_balance
  (s : String)
  (h : s.length > 0) :
  is_balanced s "xx" = ((count_char s 'x') % 2 = 0) := sorry

theorem empty_caps_always_balanced
  (s : String) :
  is_balanced s "" = true := sorry

theorem standard_parens_properties
  (s : String)
  (h : is_balanced s "()") :
  (count_char s '(' = count_char s ')') ∧ 
  ∀ (p : Nat), p ≤ s.length → 
    count_char (take_prefix s p) '(' ≥ count_char (take_prefix s p) ')' := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval is_balanced "(Sensei says yes!)" "()"

/-
info: False
-/
-- #guard_msgs in
-- #eval is_balanced "(Sensei says no!" "()"

/-
info: True
-/
-- #guard_msgs in
-- #eval is_balanced "-Hello Mother can you hear me?-" "--"

-- Apps difficulty: introductory
-- Assurance level: unguarded