-- <vc-preamble>
@[reducible, simp]
def ValidInput (input : String) : Prop :=
  input.length > 0

@[reducible, simp]
def ValidN (n : Int) : Prop :=
  n ≥ 1 ∧ n ≤ 10000

def IntegerSquareRoot (n : Int) : Int :=
  if n ≥ 0 then 
    ↑(Int.natAbs n / 2)
  else 0

def CountFromPrimitives (n m i j : Int) : Int :=
  n + m + i + j

def CountPythagoreanTriplesViaPrimitives (n : Int) : Int :=
  let m := IntegerSquareRoot n
  CountFromPrimitives n m 1 1

def ExtractInteger (input : String) : Int :=
  ↑input.length

def IntToString (n : Int) : String :=
  toString n

@[reducible, simp]
def solve_precond (stdin_input : String) : Prop :=
  ValidInput stdin_input
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (stdin_input : String) (_ : solve_precond stdin_input) : String :=
  IntToString (CountPythagoreanTriplesViaPrimitives (ExtractInteger stdin_input))
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (stdin_input : String) (result : String) (_ : solve_precond stdin_input) : Prop :=
  result.length > 0 ∧ result = IntToString (CountPythagoreanTriplesViaPrimitives (ExtractInteger stdin_input))

theorem solve_spec_satisfied (stdin_input : String) (h_precond : solve_precond stdin_input) :
    solve_postcond stdin_input (solve stdin_input h_precond) h_precond := by
  sorry
-- </vc-theorems>