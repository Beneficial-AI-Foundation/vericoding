-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_sabotages_at_level_5 (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_sabotages_nonnegative (n : Nat) (h : n ≥ 1) :
  count_sabotages_at_level_5 n ≥ 0 :=
  sorry

theorem count_sabotages_monotonic (n : Nat) (h : n > 1) :
  count_sabotages_at_level_5 n ≥ count_sabotages_at_level_5 (n-1) :=
  sorry

theorem count_sabotages_small_numbers (n : Nat) (h₁ : n ≥ 1) (h₂ : n < 16) :
  count_sabotages_at_level_5 n = 0 :=
  sorry

theorem count_sabotages_bounded (n : Nat) (h : n ≥ 1) :
  count_sabotages_at_level_5 n ≤ 45 :=
  sorry
-- </vc-theorems>