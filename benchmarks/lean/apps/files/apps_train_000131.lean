def balanced_string (s : String) : Int := sorry

def has_equal_quarters (s : String) : Bool := sorry

-- <vc-helpers>
-- </vc-helpers>

def count_char (s : String) (c : Char) : Nat := sorry

theorem invalid_length_returns_negative {s : String} :
  (s.length % 4 ≠ 0) → balanced_string s = -1 := sorry

theorem result_within_bounds {s : String} :
  balanced_string s ≠ -1 →
  0 ≤ balanced_string s ∧ balanced_string s ≤ s.length := sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval balanced_string "QWER"

/-
info: 1
-/
-- #guard_msgs in
-- #eval balanced_string "QQWE"

/-
info: 2
-/
-- #guard_msgs in
-- #eval balanced_string "QQQW"

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible