-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def digits (n : Nat) : List Nat :=
  sorry

def tidyNumber (n : Nat) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem tidy_number_returns_boolean (n : Nat) :
  tidyNumber n = true ∨ tidyNumber n = false :=
sorry

theorem single_digit_numbers_tidy (n : Nat) :
  n < 10 → tidyNumber n = true :=
sorry

theorem tidy_implies_non_decreasing_digits {n : Nat} {ds : List Nat} :
  tidyNumber n = true →
  ds = digits n →
  ∀ i j, i < j → j < ds.length → ds[i]! ≤ ds[j]! :=
sorry

theorem non_decreasing_digits_iff_tidy {n : Nat} {ds : List Nat} :
  ds = digits n →
  (∀ i j, i < j → j < ds.length → ds[i]! ≤ ds[j]!) ↔ tidyNumber n = true :=
sorry

theorem decreasing_digits_not_tidy {n : Nat} {ds : List Nat} :
  ds = digits n →
  ds.length ≥ 2 →
  (∃ i j, i < j ∧ j < ds.length ∧ ds[i]! > ds[j]!) →
  tidyNumber n = false :=
sorry
-- </vc-theorems>