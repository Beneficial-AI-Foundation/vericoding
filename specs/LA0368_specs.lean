-- <vc-preamble>
def ValidInput (N M : Int) : Prop :=
  N ≥ 1 ∧ M ≥ 1

def CountFaceDownCards (N M : Int) : Int :=
  if N = 1 ∧ M = 1 then 1
  else if N = 1 then M - 2
  else if M = 1 then N - 2
  else (N - 2) * (M - 2)

@[reducible, simp]
def solve_precond (N M : Int) : Prop :=
  ValidInput N M
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (N M : Int) (h_precond : solve_precond N M) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (N M : Int) (result : Int) (h_precond : solve_precond N M) : Prop :=
  result = CountFaceDownCards N M ∧ result ≥ 0

theorem solve_spec_satisfied (N M : Int) (h_precond : solve_precond N M) :
    solve_postcond N M (solve N M h_precond) h_precond := by
  sorry
-- </vc-theorems>