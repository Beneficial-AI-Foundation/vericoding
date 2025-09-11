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

/-
info: '9x^2'
-/
-- #guard_msgs in
-- #eval get_derivative "3x^3"

/-
info: '-3x^-2'
-/
-- #guard_msgs in
-- #eval get_derivative "3x^-1"

/-
info: '-30x^9'
-/
-- #guard_msgs in
-- #eval get_derivative "-3x^10"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded