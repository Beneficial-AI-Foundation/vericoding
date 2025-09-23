-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def compare (s1 s2 : String) : Bool := sorry

/-
The comparison of strings is case-insensitive.
In other words, comparing lowercase versions equals comparing uppercase versions.
-/
-- </vc-definitions>

-- <vc-theorems>
theorem compare_case_insensitive (s1 s2 : String) : 
  MyCompare.compare s1.toLower s2.toLower = MyCompare.compare s1.toUpper s2.toUpper := sorry

/-
The comparison is reflexive: a string equals itself.
-/

theorem compare_reflexive (s : String) :
  MyCompare.compare s s = true := sorry

/-
The comparison is symmetric: order of comparison doesn't matter.
-/

theorem compare_symmetric (s1 s2 : String) :
  MyCompare.compare s1 s2 = MyCompare.compare s2 s1 := sorry

/-
Invalid inputs compared with valid strings return false, but equal invalid inputs return true.
-/

theorem compare_invalid_input (s : String) (h : ¬s.all Char.isAlpha) :
  MyCompare.compare s "abc" = false ∧ 
  MyCompare.compare "abc" s = false ∧ 
  MyCompare.compare s s = true := sorry

end MyCompare

/-
info: True
-/
-- #guard_msgs in
-- #eval compare "AD" "BC"

/-
info: False
-/
-- #guard_msgs in
-- #eval compare "AD" "DD"

/-
info: True
-/
-- #guard_msgs in
-- #eval compare "gf" "FG"
-- </vc-theorems>