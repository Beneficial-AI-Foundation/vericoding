-- <vc-preamble>
def hammingWeight (n: Nat) : Nat := sorry

def bitLength (n: Nat) : Nat := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isPowerOfTwo (n: Nat) : Bool := sorry

theorem hamming_weight_nonnegative_and_bounded (x: Nat) : 
  hammingWeight x ≥ 0 ∧ hammingWeight x ≤ bitLength x := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem hamming_weight_power_of_two (x: Nat) :
  x > 0 → isPowerOfTwo x → hammingWeight x = 1 := sorry

theorem hamming_weight_zero_and_nonzero (x: Nat) :
  hammingWeight 0 = 0 ∧ (x > 0 → hammingWeight x > 0) := sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval hamming_weight 0

/-
info: 1
-/
-- #guard_msgs in
-- #eval hamming_weight 1

/-
info: 1
-/
-- #guard_msgs in
-- #eval hamming_weight 2

/-
info: 2
-/
-- #guard_msgs in
-- #eval hamming_weight 10

/-
info: 3
-/
-- #guard_msgs in
-- #eval hamming_weight 21

/-
info: 1
-/
-- #guard_msgs in
-- #eval hamming_weight 2048
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded