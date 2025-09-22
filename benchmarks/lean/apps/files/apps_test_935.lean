-- <vc-preamble>
def ValidInput (n m : Int) : Prop :=
  1 ≤ n ∧ n ≤ 100 ∧ 1 ≤ m ∧ m ≤ 100

def GameMoves (n m : Int) (h : ValidInput n m) : Int :=
  if n < m then n else m

def Winner (n m : Int) (h : ValidInput n m) : String :=
  let moves := GameMoves n m h
  if moves % 2 = 1 then "Akshat" else "Malvika"

@[reducible, simp]
def solve_precond (n m : Int) : Prop :=
  ValidInput n m
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n m : Int) (h_precond : solve_precond n m) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n m : Int) (result : String) (h_precond : solve_precond n m) : Prop :=
  result = Winner n m h_precond ∧ (result = "Akshat" ∨ result = "Malvika")

theorem solve_spec_satisfied (n m : Int) (h_precond : solve_precond n m) :
    solve_postcond n m (solve n m h_precond) h_precond := by
  sorry
-- </vc-theorems>