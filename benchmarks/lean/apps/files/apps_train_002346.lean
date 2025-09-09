-- <vc-helpers>
-- </vc-helpers>

def isPowerOfTwo (n: Int) : Bool :=
  sorry

theorem power_of_two_positive (n : Int) : 
  n ≤ 0 → isPowerOfTwo n = false :=
  sorry

theorem power_of_two_exactly_one_bit {n : Int} :
  n > 0 → (isPowerOfTwo n = true ↔ ∃ k, n = 2^k) :=
  sorry

theorem power_of_two_exp (k : Nat) : 
  isPowerOfTwo (2^k) = true :=
  sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval is_power_of_two 1

/-
info: True
-/
-- #guard_msgs in
-- #eval is_power_of_two 16

/-
info: False
-/
-- #guard_msgs in
-- #eval is_power_of_two 218

-- Apps difficulty: introductory
-- Assurance level: unguarded