-- <vc-helpers>
-- </vc-helpers>

def count_set_bits (n : Nat) : Nat := sorry

def count_binary_ones (n : Nat) : Nat := sorry

theorem count_set_bits_eq_binary_ones : ∀ n : Nat, 
  count_set_bits n = count_binary_ones n := sorry

theorem count_set_bits_left_shift : ∀ n : Nat, 
  n > 0 → count_set_bits (n <<< 1) = count_set_bits n := sorry

theorem count_set_bits_right_shift : ∀ n : Nat,
  n > 0 → count_set_bits (n >>> 1) = count_set_bits n - (n &&& 1) := sorry

theorem count_set_bits_or_bound : ∀ a b : Nat,
  count_set_bits (a ||| b) ≤ count_set_bits a + count_set_bits b := sorry

theorem count_set_bits_and_bound : ∀ a b : Nat,
  count_set_bits (a &&& b) ≤ min (count_set_bits a) (count_set_bits b) := sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval ways_to_shuffle 1 2 3

/-
info: 56
-/
-- #guard_msgs in
-- #eval ways_to_shuffle 369 428 797

-- Apps difficulty: interview
-- Assurance level: unguarded