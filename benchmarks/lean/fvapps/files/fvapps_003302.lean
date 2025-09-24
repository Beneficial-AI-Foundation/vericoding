-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def part_const (t k n : Nat) : Nat := sorry

theorem part_const_non_negative (t k n : Nat) :
  part_const t k n ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>