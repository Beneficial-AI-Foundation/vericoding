-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def egged (year : Nat) (span : Nat) : String ⊕ Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem egged_year_zero (span : Nat) :
  span > 0 → egged 0 span = Sum.inl "No chickens yet!" :=
sorry

theorem egged_non_negative (year span : Nat) :
  year > 0 → span > 0 → ∃ n : Nat, egged year span = Sum.inr n :=
sorry

theorem egged_monotone_span (year span : Nat) :
  year > 0 → span > 1 → 
  match egged year span, egged year (span - 1) with
  | Sum.inr n, Sum.inr m => n ≥ m
  | _, _ => False
  :=
sorry

theorem egged_first_year (year : Nat) :
  year > 0 → egged year 1 = Sum.inr 900 :=
sorry
-- </vc-theorems>