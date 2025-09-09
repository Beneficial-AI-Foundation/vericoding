-- <vc-helpers>
-- </vc-helpers>

def can_build_pyramid (bottom : String) (allowed : List String) : Bool := sorry

theorem pyramid_single_char_valid 
  (bottom : String) (allowed : List String)
  (h : bottom.length = 1) : 
  can_build_pyramid bottom allowed = true := sorry

theorem empty_rules_property
  (bottom : String) :
  can_build_pyramid bottom [] = (bottom.length = 1) := sorry

theorem duplicate_rules_irrelevant
  (bottom : String) (allowed : List String) :
  can_build_pyramid bottom allowed = can_build_pyramid bottom (allowed ++ allowed) := sorry 

theorem empty_rules_single_char
  (bottom : String) :
  can_build_pyramid bottom [] = (bottom.length = 1) := sorry

theorem known_valid_case1 :
  can_build_pyramid "ABC" ["ABC", "BCD", "CDE"] = true := sorry

theorem known_valid_case2 :
  can_build_pyramid "XY" ["XYZ"] = true := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval can_build_pyramid "XYZ" ["XYD", "YZE", "DEA", "FFF"]

/-
info: False
-/
-- #guard_msgs in
-- #eval can_build_pyramid "XXYX" ["XXX", "XXY", "XYX", "XYY", "YXZ"]

/-
info: True
-/
-- #guard_msgs in
-- #eval can_build_pyramid "ABC" ["ABC", "BCD", "CDE", "DEF"]

-- Apps difficulty: interview
-- Assurance level: unguarded