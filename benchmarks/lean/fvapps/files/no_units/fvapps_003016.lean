-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def derivative (s : String) : String := sorry

theorem derivative_constant (n : Nat) (h : n > 0 ∧ n ≤ 100) : 
  derivative s!"${n}x" = s!"${n}" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem derivative_power_rule (n : Nat) (h : n > 0 ∧ n ≤ 10) :
  derivative s!"x^${n}" = 
    if n > 2 then s!"${n}x^${n-1}"
    else if n = 2 then s!"${n}x"
    else "1" := sorry

theorem derivative_linearity (s : String) :
  ∃ result : String, derivative s = result ∧ result.length > 0 := sorry
-- </vc-theorems>