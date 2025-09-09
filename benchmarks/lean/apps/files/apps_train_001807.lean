def count_bits (n : Nat) : Array Nat := sorry

def countOnes (n : Nat) : Nat := sorry

-- <vc-helpers>
-- </vc-helpers>

def isPowerOfTwo (n : Nat) : Prop := 
  n > 0 ∧ ∃ k, n = 2^k

theorem count_bits_length (n : Nat) (h : n ≤ 1000) : 
  (count_bits n).size = n + 1 := sorry

theorem count_bits_value (n : Nat) (h : n ≤ 1000) (i : Nat) (h2 : i ≤ n) 
  (h3 : i < (count_bits n).size) :
  (count_bits n)[i]'h3 = countOnes i := sorry

theorem count_bits_power_of_two (n : Nat) (h : n ≤ 1000) (i : Nat) (h2 : i ≤ n)
  (h3 : i < (count_bits n).size) :
  i > 0 → isPowerOfTwo i → (count_bits n)[i]'h3 = 1 := sorry

/-
info: [0, 1, 1, 2, 1, 2]
-/
-- #guard_msgs in
-- #eval count_bits 5

/-
info: [0]
-/
-- #guard_msgs in
-- #eval count_bits 0

/-
info: [0, 1, 1]
-/
-- #guard_msgs in
-- #eval count_bits 2

-- Apps difficulty: interview
-- Assurance level: guarded