-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
-- </vc-definitions>

-- <vc-theorems>
theorem xor_commutative (a b : Bool) : 
  Bool.xor a b = Bool.xor b a := sorry

theorem xor_false (a : Bool) :
  Bool.xor false a = a := sorry

theorem xor_self (a : Bool) :
  Bool.xor a a = false := sorry

theorem xor_double (a b : Bool) :
  Bool.xor (Bool.xor a b) b = a := sorry

/-
info: False
-/
-- #guard_msgs in
-- #eval xor False False

/-
info: True
-/
-- #guard_msgs in
-- #eval xor True False

/-
info: True
-/
-- #guard_msgs in
-- #eval xor False True

/-
info: False
-/
-- #guard_msgs in
-- #eval xor True True
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded