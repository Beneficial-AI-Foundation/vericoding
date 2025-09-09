-- <vc-helpers>
-- </vc-helpers>

def func_or (a b : Bool) : Bool := sorry
def func_xor (a b : Bool) : Bool := sorry

theorem or_basic (a b : Bool) : 
  func_or a b = (a || b) := sorry

theorem or_commutative (a b : Bool) : 
  func_or a b = func_or b a := sorry

theorem or_identity_true (b : Bool) :
  func_or true b = true := sorry

theorem or_identity_false (b : Bool) :
  func_or false b = b := sorry

theorem xor_basic (a b : Bool) : 
  func_xor a b = (a != b) := sorry

theorem xor_commutative (a b : Bool) :
  func_xor a b = func_xor b a := sorry

theorem xor_same (a : Bool) :
  ¬(func_xor a a) := sorry

theorem xor_double (a b : Bool) :
  func_xor (func_xor a b) b = a := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval func_or True True

/-
info: True
-/
-- #guard_msgs in
-- #eval func_or True False

/-
info: False
-/
-- #guard_msgs in
-- #eval func_or False False

/-
info: True
-/
-- #guard_msgs in
-- #eval func_or 0 11

/-
info: False
-/
-- #guard_msgs in
-- #eval func_or None []

/-
info: False
-/
-- #guard_msgs in
-- #eval func_xor True True

/-
info: True
-/
-- #guard_msgs in
-- #eval func_xor True False

/-
info: False
-/
-- #guard_msgs in
-- #eval func_xor False False

/-
info: True
-/
-- #guard_msgs in
-- #eval func_xor 1 ""

/-
info: False
-/
-- #guard_msgs in
-- #eval func_xor [] None

-- Apps difficulty: introductory
-- Assurance level: unguarded