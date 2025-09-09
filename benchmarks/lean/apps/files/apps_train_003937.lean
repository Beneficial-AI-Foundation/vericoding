def mygcd (x y : Int) : Int :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def abs (x : Int) : Int :=
  sorry

theorem gcd_positive_integers {x y : Int} (hx : x > 0) (hy : y > 0) :
  let g := mygcd x y
  g > 0 ∧ x % g = 0 ∧ y % g = 0 :=
  sorry

theorem gcd_identity {x : Int} :
  mygcd x x = x :=
  sorry

theorem gcd_associative {x y : Int} (hx : x > 0) (hy : y > 0) :
  mygcd (x * y) x = x :=
  sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval mygcd 1 3

/-
info: 12
-/
-- #guard_msgs in
-- #eval mygcd 60 12

/-
info: 334
-/
-- #guard_msgs in
-- #eval mygcd 2672 5678

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible