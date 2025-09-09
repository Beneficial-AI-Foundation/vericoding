-- <vc-helpers>
-- </vc-helpers>

def stringContains (s1 s2 : String) : Bool := sorry

def actually_really_good (foods : List String) : String := sorry

theorem actually_really_good_prefix (foods : List String) :
  String.startsWith (actually_really_good foods) "You know what's actually really good? " := sorry

theorem actually_really_good_empty_list :
  actually_really_good [] = "You know what's actually really good? Nothing!" := sorry

theorem actually_really_good_handles_duplicates (food : String) :
  actually_really_good [food, food] = actually_really_good [food] := sorry

/-
info: "You know what's actually really good? Nothing!"
-/
-- #guard_msgs in
-- #eval actually_really_good []

/-
info: "You know what's actually really good? Peanut butter and more peanut butter."
-/
-- #guard_msgs in
-- #eval actually_really_good ["Peanut butter"]

/-
info: "You know what's actually really good? Ice cream and ham."
-/
-- #guard_msgs in
-- #eval actually_really_good ["Ice cream", "Ham"]

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible