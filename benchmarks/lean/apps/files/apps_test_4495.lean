-- <vc-preamble>
def ValidInput (a b x : Int) : Prop :=
  a ≥ 0 ∧ b ≥ a ∧ x > 0

def CountDivisibleInRange (a b x : Int) (h : ValidInput a b x) : Int :=
  if a = 0 then
    b / x + 1
  else
    b / x - (a - 1) / x

@[reducible, simp]
def solve_precond (a b x : Int) : Prop :=
  ValidInput a b x
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (a b x : Int) (h_precond : solve_precond a b x) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (a b x : Int) (count : Int) (h_precond : solve_precond a b x) : Prop :=
  count = CountDivisibleInRange a b x h_precond ∧ count ≥ 0

theorem solve_spec_satisfied (a b x : Int) (h_precond : solve_precond a b x) :
    solve_postcond a b x (solve a b x h_precond) h_precond := by
  sorry
-- </vc-theorems>