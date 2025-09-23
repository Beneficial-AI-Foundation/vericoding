-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sqrt (n : Nat) : Nat :=
  sorry

def predict_age (ages : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem predict_age_non_negative (ages : List Nat) :
  0 ≤ predict_age ages :=
sorry

theorem predict_age_is_nat (ages : List Nat) :
  predict_age ages = predict_age ages :=
sorry

theorem predict_age_order_independent (ages : List Nat) :
  predict_age ages = predict_age ages.reverse :=
sorry

theorem predict_age_zero :
  predict_age [0] = 0 :=
sorry

theorem predict_age_single (age : Nat) :
  predict_age [age] = age / 2 :=
sorry
-- </vc-theorems>