-- <vc-preamble>
def ValidInput (a b x : Int) : Prop :=
  1 ≤ a ∧ a ≤ 100 ∧ 1 ≤ b ∧ b ≤ 100 ∧ 1 ≤ x ∧ x ≤ 200

def CanHaveExactlyCats (a b x : Int) : Prop :=
  a ≤ x ∧ x ≤ a + b

@[reducible, simp]
def solve_precond (a b x : Int) : Prop :=
  ValidInput a b x
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (a b x : Int) (h_precond : solve_precond a b x) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (a b x : Int) (result : String) (h_precond : solve_precond a b x) : Prop :=
  (result = "YES") ↔ CanHaveExactlyCats a b x

theorem solve_spec_satisfied (a b x : Int) (h_precond : solve_precond a b x) :
    solve_postcond a b x (solve a b x h_precond) h_precond := by
  sorry
-- </vc-theorems>