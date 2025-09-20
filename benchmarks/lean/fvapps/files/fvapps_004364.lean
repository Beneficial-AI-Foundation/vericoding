-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def finance (n : Int) : Int := sorry

theorem finance_non_negative (n : Nat) :
  finance n ≥ 0 ∧ 
  finance n = n * (n + 1) * (n + 2) / 2 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem finance_strictly_increasing {n : Nat} (h : n > 0) :
  finance n > finance (n - 1) := sorry
-- </vc-theorems>