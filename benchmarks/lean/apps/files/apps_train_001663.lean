def Term := String
def Equation := String

def Solution := List (String × Int)

def solve_equations : List Equation → Option Solution
  | _ => sorry

def equation_vars : Equation → List String 
  | _ => sorry

def solution_vars : Solution → List String
  | _ => sorry

-- <vc-helpers>
-- </vc-helpers>

def verify_solution (equations : List Equation) (solution : Option Solution) : Bool :=
sorry

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

/-
info: expected1
-/
-- #guard_msgs in
-- #eval solve_equations ["2x + 4y + 6z = 18", "3y + 3z = 6", "x + 2y = z - 3"]

/-
info: None
-/
-- #guard_msgs in
-- #eval solve_equations ["x + y = 2", "x + y = 3"]

/-
info: expected3
-/
-- #guard_msgs in
-- #eval solve_equations ["x = 1"]

-- Apps difficulty: interview
-- Assurance level: unguarded