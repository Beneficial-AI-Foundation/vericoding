def isLower (c : Char) : Bool := sorry
def isUpper (c : Char) : Bool := sorry

-- <vc-helpers>
-- </vc-helpers>

def tv_remote (s : String) : Nat := sorry

theorem tv_remote_basic_properties (s : String) : tv_remote s ≥ 0 := sorry

theorem tv_remote_empty_string : tv_remote "" = 0 := sorry 

theorem tv_remote_case_sensitivity (s : String) :
  s ≠ "" → tv_remote (s.map Char.toUpper) ≥ tv_remote (s.map Char.toLower) := sorry

/-
info: 69
-/
-- #guard_msgs in
-- #eval tv_remote "Code Wars"

/-
info: 12
-/
-- #guard_msgs in
-- #eval tv_remote "A"

/-
info: 16
-/
-- #guard_msgs in
-- #eval tv_remote "does"

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible