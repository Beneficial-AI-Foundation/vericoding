/-
This kata is about multiplying a given number by eight if it is an even number and by nine otherwise.
-/

-- <vc-helpers>
-- </vc-helpers>

def simple_multiplication (n : Int) : Int := sorry

theorem simple_multiplication_even (n : Int) 
  (h : n % 2 = 0) : 
  simple_multiplication n = n * 8 := sorry

theorem simple_multiplication_odd (n : Int)
  (h : n % 2 = 1) :
  simple_multiplication n = n * 9 := sorry

/-
info: 16
-/
-- #guard_msgs in
-- #eval simple_multiplication 2

/-
info: 9
-/
-- #guard_msgs in
-- #eval simple_multiplication 1

/-
info: 64
-/
-- #guard_msgs in
-- #eval simple_multiplication 8

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible