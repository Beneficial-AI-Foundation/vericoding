-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def values (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem values_nonneg (n : Nat) : values n ≥ 0 :=
  sorry

theorem values_is_nat (n : Nat) : values n = values n :=
  sorry

theorem values_edge_cases : 
  values 1 = 0 ∧ 
  values 100 = 3 ∧ 
  values 1000 = 11 ∧
  values 10000000 > 0 :=
  sorry

theorem values_small_range (n : Nat) :
  n > 0 → n ≤ 1000 → values n ≥ 0 :=
  sorry
-- </vc-theorems>