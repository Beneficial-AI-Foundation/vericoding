-- <vc-preamble>

def ValidInput (n a b : Int) : Prop :=
  n > 0 ∧ a > 0 ∧ b > 0

def ValidOutput (result : List Int) (n a b : Int) : Prop :=
  result.length = 3 ∧
  result[0]! ≥ 6 * n ∧
  result[1]! > 0 ∧ result[2]! > 0 ∧
  result[0]! = result[1]! * result[2]! ∧
  ((result[1]! ≥ a ∧ result[2]! ≥ b) ∨ (result[1]! ≥ b ∧ result[2]! ≥ a))

@[reducible, simp]
def solve_precond (n a b : Int) : Prop :=
  ValidInput n a b
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n a b : Int) (h_precond : solve_precond n a b) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n a b : Int) (result : List Int) (h_precond : solve_precond n a b) : Prop :=
  ValidOutput result n a b

theorem solve_spec_satisfied (n a b : Int) (h_precond : solve_precond n a b) :
    solve_postcond n a b (solve n a b h_precond) h_precond := by
  sorry
-- </vc-theorems>