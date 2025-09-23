-- <vc-preamble>
def ValidInput (H W h w : Int) : Prop :=
  1 ≤ H ∧ H ≤ 20 ∧ 1 ≤ W ∧ W ≤ 20 ∧ 1 ≤ h ∧ h ≤ H ∧ 1 ≤ w ∧ w ≤ W

def WhiteCellsRemaining (H W h w : Int) : Int :=
  (H - h) * (W - w)

@[reducible, simp]
def solve_precond (H W h w : Int) : Prop :=
  ValidInput H W h w
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (H W h w : Int) (h_precond : solve_precond H W h w) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (H W h w : Int) (result: Int) (h_precond : solve_precond H W h w) : Prop :=
  result = WhiteCellsRemaining H W h w ∧ result ≥ 0

theorem solve_spec_satisfied (H W h w : Int) (h_precond : solve_precond H W h w) :
    solve_postcond H W h w (solve H W h w h_precond) h_precond := by
  sorry
-- </vc-theorems>