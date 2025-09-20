-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_derivative : String → String := sorry

theorem derivative_polynomial_form (expr : String) 
  (h : ∃ a b : Int, a ≠ 0 ∧ (expr = s!"{a}x^{b}" ∨ expr = s!"{a}x")) :
  ∃ result : String, get_derivative expr = result ∧ 
  (result.any (· = 'x') ∨ result = "0") := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem simple_power_rule (n : Int) (h : n ≠ 0) :
  get_derivative s!"1x^{n}" = 
    if n - 1 = 1 
    then s!"{n}x"
    else s!"{n}x^{n-1}" := sorry

theorem constant_term (n : Int) (h : n ≠ 0) :
  get_derivative (toString n) = "0" := sorry

theorem linear_term (n : Int) (h : n ≠ 0) :
  get_derivative s!"{n}x" = toString n := sorry
-- </vc-theorems>