def binary_gcd (x y : Int) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def popCount (n : Nat) : Nat :=
  sorry

theorem binary_gcd_matches_gcd (x y : Int) :
  binary_gcd x y = popCount (Int.gcd x y) :=
  sorry

theorem binary_gcd_symmetric_same (n : Int) :
  binary_gcd n n = binary_gcd n (-n) :=
  sorry

theorem binary_gcd_symmetric_zero (n : Int) :
  binary_gcd n 0 = binary_gcd 0 n :=
  sorry

theorem binary_gcd_positive_bounds (x y : Int) (hx : x > 0) (hy : y > 0) :
  let result := binary_gcd x y
  0 ≤ result ∧ result ≤ max x.natAbs.log2 y.natAbs.log2 :=
  sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval binary_gcd 300 45

/-
info: 0
-/
-- #guard_msgs in
-- #eval binary_gcd 0 0

/-
info: 1
-/
-- #guard_msgs in
-- #eval binary_gcd -8 12

-- Apps difficulty: introductory
-- Assurance level: unguarded