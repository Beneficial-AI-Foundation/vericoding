def spreadsheet (s : String) : String := sorry

def is_valid_a1 (s : String) : Bool := sorry

-- <vc-helpers>
-- </vc-helpers>

def is_valid_r1c1 (s : String) : Bool := sorry

theorem a1_conversion {s : String} (h : is_valid_a1 s = true) : 
  is_valid_r1c1 (spreadsheet s) = true ∧ 
  spreadsheet (spreadsheet s) = s := sorry

theorem r1c1_conversion {s : String} (h : is_valid_r1c1 s = true) :
  is_valid_a1 (spreadsheet s) = true ∧
  spreadsheet (spreadsheet s) = s := sorry

theorem conversion_idempotent_a1 {s : String} (h : is_valid_a1 s = true) :
  spreadsheet (spreadsheet s) = s := sorry

theorem conversion_idempotent_r1c1 {s : String} (h : is_valid_r1c1 s = true) :
  spreadsheet (spreadsheet s) = s := sorry

/-
info: 'R1C1'
-/
-- #guard_msgs in
-- #eval spreadsheet "A1"

/-
info: 'AA48'
-/
-- #guard_msgs in
-- #eval spreadsheet "R48C27"

/-
info: 'R12C63'
-/
-- #guard_msgs in
-- #eval spreadsheet "BK12"

-- Apps difficulty: introductory
-- Assurance level: unguarded