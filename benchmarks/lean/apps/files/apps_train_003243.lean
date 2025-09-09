-- <vc-helpers>
-- </vc-helpers>

def f (n : Nat) : Nat := sorry

def isPrime (n : Nat) : Bool := sorry

theorem f_always_positive (n : Nat) (h : n > 0) : 
  f n > 0 := sorry

/-
info: 4200
-/
-- #guard_msgs in
-- #eval f 24500

/-
info: 1
-/
-- #guard_msgs in
-- #eval f 997

/-
info: 10
-/
-- #guard_msgs in
-- #eval f 25

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible