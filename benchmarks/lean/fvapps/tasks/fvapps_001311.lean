-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_remove_for_kgood (s : String) (k : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_remove_nonnegative (s : String) (k : Nat) :
  min_remove_for_kgood s k ≥ 0 :=
sorry

theorem min_remove_bounded (s : String) (k : Nat) :
  min_remove_for_kgood s k ≤ s.length :=
sorry

theorem min_remove_large_k (s : String) (k : Nat) :
  s.length > 0 →
  k ≥ s.length →
  min_remove_for_kgood s k = 0 :=
sorry

theorem min_remove_single_char (s : String) :
  s.length = 1 →
  min_remove_for_kgood s 0 = 0 :=
sorry

theorem min_remove_empty_string :
  ∀ k, min_remove_for_kgood "" k = 0 :=
sorry
-- </vc-theorems>