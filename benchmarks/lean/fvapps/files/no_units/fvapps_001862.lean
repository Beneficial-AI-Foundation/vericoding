-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_equation (eq : String) : String := sorry

theorem simple_integer_solutions (n : Int) : 
  solve_equation s!"x={n}" = s!"x={n}" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem linear_equation_solution (a b : Int) (h : a ≠ 0) :
  solve_equation s!"{a}x={b}" = if b % a = 0 then s!"x={b/a}" else "No solution" := sorry

theorem special_cases_identities :
  solve_equation "x=x" = "Infinite solutions" ∧
  solve_equation "0x=0" = "Infinite solutions" ∧
  solve_equation "0x=1" = "No solution" ∧ 
  solve_equation "2x=x" = "x=0" ∧
  solve_equation "-x=x" = "x=0" := sorry

theorem solution_validity (eq result : String) :
  solve_equation eq = result →
  (result = "No solution" ∨
   result = "Infinite solutions" ∨
   ∃ x:Int, result = s!"x={x}" ∧ 
   -- The solution x satisfies the original equation
   sorry) := sorry
-- </vc-theorems>