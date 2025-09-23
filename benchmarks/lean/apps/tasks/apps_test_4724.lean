-- <vc-preamble>
def ValidInput (R G : Int) : Prop :=
  0 ≤ R ∧ R ≤ 4500 ∧ 0 ≤ G ∧ G ≤ 4500

def RequiredPerformance (R G : Int) : Int :=
  2 * G - R

def CorrectResult (R G P : Int) : Prop :=
  (R + P) = 2 * G

@[reducible, simp]
def solve_precond (R G : Int) : Prop :=
  ValidInput R G
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (R G : Int) (h_precond : solve_precond R G) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (R G : Int) (result: Int) (h_precond : solve_precond R G) : Prop :=
  result = RequiredPerformance R G ∧ CorrectResult R G result

theorem solve_spec_satisfied (R G : Int) (h_precond : solve_precond R G) :
    solve_postcond R G (solve R G h_precond) h_precond := by
  sorry
-- </vc-theorems>