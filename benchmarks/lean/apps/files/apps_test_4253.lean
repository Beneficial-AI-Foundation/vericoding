-- <vc-preamble>
def ValidInput (r : Int) : Prop :=
  1 ≤ r ∧ r ≤ 100

def DodecagonArea (r : Int) : Int :=
  3 * r * r

def int_to_string (n : Int) : String :=
  toString n

def string_to_int (s : String) : Int :=
  s.toInt!

@[reducible, simp]
def solve_precond (stdin_input : String) : Prop :=
  stdin_input.length > 0 ∧ 
  ∃ r : Int, ValidInput r ∧ 
  (stdin_input = int_to_string r ∨ stdin_input = int_to_string r ++ "\n")
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (stdin_input : String) (h_precond : solve_precond stdin_input) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (stdin_input : String) (output : String) (h_precond : solve_precond stdin_input) : Prop :=
  ∃ r : Int, ValidInput r ∧
  (stdin_input = int_to_string r ∨ stdin_input = int_to_string r ++ "\n") ∧
  output = int_to_string (DodecagonArea r) ++ "\n"

theorem solve_spec_satisfied (stdin_input : String) (h_precond : solve_precond stdin_input) :
    solve_postcond stdin_input (solve stdin_input h_precond) h_precond := by
  sorry
-- </vc-theorems>