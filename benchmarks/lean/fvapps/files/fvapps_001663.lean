-- <vc-preamble>
def Term := String

def Equation := String

def Solution := List (String × Int)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_equations : List Equation → Option Solution :=
  sorry

def equation_vars : Equation → List String :=
  sorry

def solution_vars : Solution → List String :=
  sorry

def verify_solution (equations : List Equation) (solution : Option Solution) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solution_variables_match_equations (equations : List Equation)
  (s : Solution)
  (h : solve_equations equations = some s) :
  ∀ v, (∃ eq ∈ equations, v ∈ equation_vars eq) ↔ v ∈ solution_vars s :=
sorry

theorem underdetermined_system_no_solution :
  solve_equations ["x + y = 1"] = none :=
sorry

theorem solution_satisfies_equations (equations : List Equation)
  (s : Solution)
  (h : solve_equations equations = some s) :
  verify_solution equations (some s) = true :=
sorry
-- </vc-theorems>