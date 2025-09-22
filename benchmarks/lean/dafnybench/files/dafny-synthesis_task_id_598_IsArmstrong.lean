-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def IsArmstrong (n : Int) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem IsArmstrong_spec (n : Int) :
100 ≤ n ∧ n < 1000 →
IsArmstrong n = (n = ((n / 100) * (n / 100) * (n / 100) +
((n / 10) % 10) * ((n / 10) % 10) * ((n / 10) % 10) +
(n % 10) * (n % 10) * (n % 10))) :=
sorry
-- </vc-theorems>