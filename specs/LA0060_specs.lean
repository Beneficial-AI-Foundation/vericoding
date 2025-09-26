-- <vc-preamble>
def ValidInput (n a : Int) : Prop :=
  n > 0 ∧ n % 2 = 0 ∧ 1 ≤ a ∧ a ≤ n

def DistanceToHouse (n a : Int) : Int :=
  if a % 2 = 1 then
    a / 2 + 1
  else
    (n - a) / 2 + 1

@[reducible, simp]
def solve_precond (n a : Int) : Prop :=
  ValidInput n a
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n a : Int) (h_precond : solve_precond n a) : Int :=
  DistanceToHouse n a
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n a : Int) (result: Int) (h_precond : solve_precond n a) : Prop :=
  result > 0

theorem solve_spec_satisfied (n a : Int) (h_precond : solve_precond n a) :
    solve_postcond n a (solve n a h_precond) h_precond := by
  sorry
-- </vc-theorems>