def next_higher (n : Nat) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def countOnes (n : Nat) : Nat :=
  sorry

theorem next_higher_preserves_bit_count (n : Nat) (h : n > 0) (h2 : n < 2^16) :
  countOnes n = countOnes (next_higher n) :=
  sorry

theorem next_higher_is_higher (n : Nat) (h : n > 0) (h2 : n < 2^16) :
  next_higher n > n :=
  sorry

theorem next_higher_power_two (i : Nat) (h : i < 8) :
  next_higher (2^i) = 2^(i+1) :=
  sorry

/-
info: 256
-/
-- #guard_msgs in
-- #eval next_higher 128

/-
info: 191
-/
-- #guard_msgs in
-- #eval next_higher 127

/-
info: 2
-/
-- #guard_msgs in
-- #eval next_higher 1

-- Apps difficulty: introductory
-- Assurance level: unguarded