-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_xor_pairs (x y n : Nat) : Nat := sorry 

theorem count_xor_pairs_equal_nums {x n : Nat} :
  count_xor_pairs x x n = 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_xor_pairs_nonneg {x y n : Nat} :
  count_xor_pairs x y n ≥ 0 := sorry

theorem count_xor_pairs_upper_bound {x y n : Nat} :
  count_xor_pairs x y n ≤ n + 1 := sorry

theorem count_xor_pairs_complement {x y n : Nat} (h : x ≠ y) :
  count_xor_pairs x y n + count_xor_pairs y x n = n + 1 := sorry

theorem count_xor_pairs_monotonic {x y n₁ n₂ : Nat} (h : n₁ ≤ n₂) :
  count_xor_pairs x y n₁ ≤ count_xor_pairs x y n₂ := sorry
-- </vc-theorems>