-- <vc-preamble>
def ValidInput (n a : Int) : Prop :=
  1 ≤ n ∧ n ≤ 10000 ∧ 0 ≤ a ∧ a ≤ 1000

def CanPayExactly (n a : Int) : Prop :=
  n % 500 ≤ a

def ValidOutput (result : String) : Prop :=
  result = "Yes" ∨ result = "No"

@[reducible, simp]
def solve_precond (n a : Int) : Prop :=
  ValidInput n a
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n a : Int) (h_precond : solve_precond n a) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n a : Int) (result : String) (h_precond : solve_precond n a) : Prop :=
  ValidOutput result ∧ (result = "Yes" ↔ CanPayExactly n a)

theorem solve_spec_satisfied (n a : Int) (h_precond : solve_precond n a) :
    solve_postcond n a (solve n a h_precond) h_precond := by
  sorry
-- </vc-theorems>