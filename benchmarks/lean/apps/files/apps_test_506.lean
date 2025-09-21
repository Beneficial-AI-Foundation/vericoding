-- <vc-preamble>
def ValidInput (a b : Int) : Prop :=
  a > 0 ∧ b > 0

partial def countSquares (a b : Int) : Int :=
  if a = 0 ∨ b = 0 then 0
  else if a > b then a / b + countSquares (a % b) b
  else b / a + countSquares a (b % a)

@[reducible, simp]
def solve_precond (a b : Int) : Prop :=
  ValidInput a b
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (a b : Int) (h_precond : solve_precond a b) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (a b : Int) (result : Int) (h_precond : solve_precond a b) : Prop :=
  result ≥ 0 ∧ 
  (a = b → result = 1) ∧
  (a > b → result ≥ 1) ∧
  result = countSquares a b

theorem solve_spec_satisfied (a b : Int) (h_precond : solve_precond a b) :
    solve_postcond a b (solve a b h_precond) h_precond := by
  sorry
-- </vc-theorems>