-- <vc-preamble>
noncomputable def power (n : Nat) (alpha : Float ) : Float :=
sorry

noncomputable def log (n : Nat) (alpha : Float) : Float :=
sorry

noncomputable def pow (n : Nat) (alpha : Float) : Float :=
sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
-- </vc-definitions>

-- <vc-theorems>
theorem power_spec (n : Nat) (alpha : Float) :
n > 0 ∧ alpha > 0 → power n alpha > 0 :=
sorry

theorem log_spec (n : Nat) (alpha : Float) :
n > 0 ∧ alpha > 0 → log n alpha > 0 :=
sorry

theorem pow_spec (n : Nat) (alpha : Float) :
n > 0 ∧ alpha > 0 → pow n alpha = power (n) alpha :=
sorry
-- </vc-theorems>