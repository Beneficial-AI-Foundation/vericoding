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

/-
info: 6
-/
-- #guard_msgs in
-- #eval count_xor_pairs 1 2 10

/-
info: 5
-/
-- #guard_msgs in
-- #eval count_xor_pairs 2 1 10

/-
info: 0
-/
-- #guard_msgs in
-- #eval count_xor_pairs 0 0 7
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible