def count_ones_in_binary (n : Int) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def count_bits : Int → Nat :=
  fun n => if n = 0 then 0 else (n % 2).natAbs + count_bits (n / 2)
decreasing_by sorry

theorem count_ones_nonnegative_basic {x : Int} (h : x ≥ 0) :
  count_ones_in_binary x ≥ 0 :=
  sorry

theorem count_ones_negative_has_ones {x : Int} (h : x < 0) :
  count_ones_in_binary x > 0 :=
  sorry

theorem count_ones_power_of_two {x : Int} (h1 : x > 0) (h2 : x % 2 = 0) :
  count_ones_in_binary x = 1 :=
  sorry

theorem count_ones_equals_bit_count {x : Int} (h : x ≥ 0) :
  count_ones_in_binary x = count_bits x :=
  sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval count_ones_in_binary test_input[0]

/-
info: 2
-/
-- #guard_msgs in
-- #eval count_ones_in_binary test_input[0]

/-
info: 3
-/
-- #guard_msgs in
-- #eval count_ones_in_binary test_input[0]

-- Apps difficulty: interview
-- Assurance level: unguarded