-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def cheapest_quote (n : Nat) : Float :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem cheapest_quote_non_negative (n : Nat) :
  let result := cheapest_quote n
  result ≥ 0 :=
sorry

theorem cheapest_quote_monotonic (n : Nat) : n > 0 →
  cheapest_quote n > cheapest_quote (n-1) :=
sorry
-- </vc-theorems>