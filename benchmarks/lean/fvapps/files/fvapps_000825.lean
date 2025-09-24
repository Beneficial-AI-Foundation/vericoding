-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def harry_biscuits (K A B : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem harry_biscuits_positive (K A B : Nat) : 
  A > 0 → B > 0 → harry_biscuits K A B ≥ 0 :=
  sorry

theorem harry_biscuits_no_exchange (K A B : Nat) :
  A > 0 → B > 0 → A + 2 > B → harry_biscuits K A B = K + 1 :=
  sorry

theorem harry_biscuits_small_k (K A B : Nat) :
  A > 0 → B > 0 → K < A - 1 → harry_biscuits K A B = min (K + 1) A :=
  sorry

theorem harry_biscuits_small_b (K A B : Nat) :
  A > 0 → B > 0 → B ≤ A + 2 → harry_biscuits K A B = K + 1 :=
  sorry

theorem harry_biscuits_zero_k :
  harry_biscuits 0 5 10 = 1 :=
  sorry

theorem harry_biscuits_equal_exchange :
  harry_biscuits 4 3 5 = 5 :=
  sorry

theorem harry_biscuits_no_profitable_exchange (K : Nat) :
  harry_biscuits K 5 7 = K + 1 :=
  sorry
-- </vc-theorems>