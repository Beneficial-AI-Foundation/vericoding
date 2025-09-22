-- <vc-preamble>
def count_bits : Nat → Nat :=
  fun n => if n = 0 then 0 else (n % 2) + count_bits (n / 2)
decreasing_by all_goals simp_wf; omega
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_ones_in_binary (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_ones_nonnegative_basic {x : Nat} (h : x ≥ 0) :
  count_ones_in_binary x ≥ 0 :=
  sorry

theorem count_ones_negative_has_ones {x : Nat} (h : x < 0) :
  count_ones_in_binary x > 0 :=
  sorry

theorem count_ones_power_of_two {x : Nat} (h1 : x > 0) (h2 : x % 2 = 0) :
  count_ones_in_binary x = 1 :=
  sorry

theorem count_ones_equals_bit_count {x : Nat} (h : x ≥ 0) :
  count_ones_in_binary x = count_bits x :=
  sorry
-- </vc-theorems>