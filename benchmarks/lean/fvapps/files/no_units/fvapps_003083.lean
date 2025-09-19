-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def cheapest_quote (n : Nat) : Float := sorry

/- Ensures cheapest_quote returns a non-negative float -/
-- </vc-definitions>

-- <vc-theorems>
theorem cheapest_quote_non_negative (n : Nat) :
  let result := cheapest_quote n
  result ≥ 0 := sorry
-- </vc-theorems>