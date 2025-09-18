-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def differentiate_polynomial (terms : List (Int × Nat)) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem derivative_formatting_empty_or_constant (terms : List (Int × Nat)) :
  (terms.isEmpty ∨ terms.all (fun t => t.2 = 0)) →
  differentiate_polynomial terms = "0" :=
sorry

theorem derivative_formatting_valid (terms : List (Int × Nat)) :
  ¬terms.isEmpty →
  ∃ parts : List String,
    differentiate_polynomial terms ≠ "0" →
    (∀ part, part ∈ parts → 
      (∃ c e : String, part = c ++ "x^" ++ e) ∨
      (∃ c : String, part = c)) :=
sorry

theorem derivative_rules_constant (coef : Int) :
  differentiate_polynomial [(coef, 0)] = "0" :=
sorry

theorem derivative_rules_linear (coef : Int) :
  coef ≠ 0 →
  differentiate_polynomial [(coef, 1)] = toString coef :=
sorry

theorem derivative_rules_power (coef : Int) (exp : Nat) :
  coef ≠ 0 →
  exp > 1 →
  let deriv := differentiate_polynomial [(coef, exp)]
  if exp - 1 = 0 then
    deriv = toString (coef * exp)
  else
    deriv = toString (coef * exp) ++ "x^" ++ toString (exp - 1) :=
sorry

theorem derivative_ordering (terms : List (Int × Nat)) (i j : Nat) :
  differentiate_polynomial terms ≠ "0" →
  let parts := (differentiate_polynomial terms).split (· = ' ')
  let exponents := parts.map (fun p =>
    if p.contains 'x' then
      (p.split (· = '^')).getLast!
    else "0")
  i < j → i < exponents.length → j < exponents.length →
  String.toNat! (exponents[i]!) ≥ String.toNat! (exponents[j]!) :=
sorry
-- </vc-theorems>