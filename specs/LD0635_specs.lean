-- <vc-preamble>
partial def fact (n : Nat) : Nat :=
if n == 0 then 1 else n * fact (n - 1)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def factorial (n : Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem fact_spec (n : Nat) : fact n ≥ 1 :=
sorry

theorem factorial_spec (n : Nat) : factorial n = fact n :=
sorry
-- </vc-theorems>