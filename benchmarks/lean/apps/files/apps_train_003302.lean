-- <vc-helpers>
-- </vc-helpers>

def part_const (t k n : Nat) : Nat := sorry

theorem part_const_non_negative (t k n : Nat) :
  part_const t k n ≥ 0 := sorry

theorem larger_parts_zero (t k : Nat) (h : k > t) :
  part_const t k n = 0 := sorry

theorem forbidden_decreases_count (t k n : Nat) (h : n > 0) :
  part_const t k 0 ≥ part_const t k n := sorry

theorem large_forbidden_same (t k : Nat) :
  part_const t k (t+1) = part_const t k 0 := sorry

theorem single_partition_count (t : Nat) :
  part_const t 1 0 = 1 := sorry

theorem single_partition_forbidden (t : Nat) (h : t > 1) :
  part_const t 1 t = 0 := sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval part_const 10 3 2

/-
info: 8
-/
-- #guard_msgs in
-- #eval part_const 10 3 0

/-
info: 15
-/
-- #guard_msgs in
-- #eval part_const 15 5 3

-- Apps difficulty: introductory
-- Assurance level: guarded