-- <vc-preamble>
def calculateDeposit (initial : Int) (years : Nat) : Int :=
  if years = 0 then initial
  else 
    let prevDeposit := calculateDeposit initial (years - 1)
    prevDeposit + prevDeposit / 100

@[reducible, simp]
def solve_precond (X : Int) : Prop :=
  X ≥ 101
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (X : Int) (h_precond : solve_precond X) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (X : Int) (years : Int) (h_precond : solve_precond X) : Prop :=
  years ≥ 0 ∧ 
  (let finalDeposit := calculateDeposit 100 (Int.natAbs years); finalDeposit ≥ X) ∧
  (years = 0 ∨ calculateDeposit 100 (Int.natAbs (years - 1)) < X)

theorem solve_spec_satisfied (X : Int) (h_precond : solve_precond X) :
    solve_postcond X (solve X h_precond) h_precond := by
  sorry
-- </vc-theorems>