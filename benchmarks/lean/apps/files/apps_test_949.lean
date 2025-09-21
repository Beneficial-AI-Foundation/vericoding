-- <vc-preamble>
def ValidInput (a b : Int) : Prop :=
  1 ≤ a ∧ a ≤ b

def GcdOfRange (a b : Int) (h : ValidInput a b) : Int :=
  if a = b then a else 1

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
  result = GcdOfRange a b h_precond ∧ 
  (a = b → result = a) ∧ 
  (a < b → result = 1)

theorem solve_spec_satisfied (a b : Int) (h_precond : solve_precond a b) :
    solve_postcond a b (solve a b h_precond) h_precond := by
  sorry
-- </vc-theorems>