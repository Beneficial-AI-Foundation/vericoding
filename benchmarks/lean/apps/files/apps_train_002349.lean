-- <vc-helpers>
-- </vc-helpers>

def countPrimes (n : Int) : Int := sorry

theorem countPrimes_nonnegative (x : Int) :
  countPrimes x ≥ 0 := sorry

theorem countPrimes_monotonic (x : Int) :
  x > 0 → countPrimes x ≥ countPrimes (x - 1) := sorry

theorem countPrimes_less_than_input (x : Int) :
  x ≥ 2 → countPrimes x < x := sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval countPrimes 10

/-
info: 8
-/
-- #guard_msgs in
-- #eval countPrimes 20

/-
info: 25
-/
-- #guard_msgs in
-- #eval countPrimes 100

-- Apps difficulty: introductory
-- Assurance level: unguarded