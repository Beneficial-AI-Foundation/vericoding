-- <vc-preamble>
partial def power (a n : Int) : Int :=
if n = 0 then 1 else a * power a (n - 1)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def compute_power (a n : Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem power_spec (a n : Int) :
a ≥ 0 ∧ n ≥ 0 → power a n ≥ 0 :=
sorry

theorem compute_power_spec (a n : Int) :
a ≥ 0 ∧ n ≥ 0 → compute_power a n = power a n :=
sorry
-- </vc-theorems>