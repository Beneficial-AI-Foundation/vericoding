-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_arrays (d : Nat) (m : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_arrays_range (d m : Nat) (hd : d > 0) (hm : m > 0) :
  count_arrays d m < m := sorry

theorem count_arrays_nonneg (d m : Nat) (hd : d > 0) (hm : m > 0) :
  count_arrays d m ≥ 0 := sorry

theorem count_arrays_base_case (d : Nat) (hd : d > 0) :
  count_arrays d 1 = 0 := sorry

theorem count_arrays_monotonic (d m : Nat) (hd : d > 0) (hm : m > 1) :
  count_arrays d m ≤ count_arrays (d+1) m ∨ 
  (count_arrays (d+1) m) % m < (count_arrays d m) % m := sorry

theorem count_arrays_small_known_1 :
  count_arrays 1 1000000000 = 1 := sorry

theorem count_arrays_small_known_2 :
  count_arrays 2 1000000000 = 3 := sorry
-- </vc-theorems>