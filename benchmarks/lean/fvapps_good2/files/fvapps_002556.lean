-- <vc-preamble>
def valid_roles : List String :=
  ["Boss", "Truck Driver", "Warehouse Manager", "Sales Assistant",
   "Admin", "Sales Manager", "Warehouse Picker", "Receptionist", "Trainee"]
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_employees_role (name : String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem known_employee_roles_are_valid (name : String) (h : name.length > 0) :
  let role := find_employees_role name
  role = "Does not work here!" ∨ role ∈ valid_roles :=
sorry

theorem returns_string (name : String) (h : name.length > 0) :
  String.length (find_employees_role name) > 0 :=
sorry

theorem unknown_single_name_returns_not_found (name : String) (h1 : name.length > 0)
    (h2 : ¬(name.contains ' ')) :
  find_employees_role name = "Does not work here!" :=
sorry

theorem name_order_matters (first last : String)
    (h1 : first.length > 0) (h2 : last.length > 0) :
  let role1 := find_employees_role (first ++ " " ++ last)
  let role2 := find_employees_role (last ++ " " ++ first)
  (role1 ≠ "Does not work here!" ∧ role2 ≠ "Does not work here!") →
  role1 ≠ role2 :=
sorry
-- </vc-theorems>