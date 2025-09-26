-- <vc-preamble>
def computePosition (days v0 v1 a l : Int) : Int :=
  if days ≤ 0 then 0
  else
    let prevPos := computePosition (days - 1) v0 v1 a l
    let afterReread := if prevPos - l > 0 then prevPos - l else 0
    let readToday := if v1 < v0 + a * (days - 1) then v1 else v0 + a * (days - 1)
    afterReread + readToday
termination_by days.natAbs
decreasing_by 
  simp_wf
  omega

@[reducible, simp]
def solve_precond (c v0 v1 a l : Int) : Prop :=
  1 ≤ c ∧ c ≤ 1000 ∧ 0 ≤ l ∧ l < v0 ∧ v0 ≤ v1 ∧ v1 ≤ 1000 ∧ 0 ≤ a ∧ a ≤ 1000
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (c v0 v1 a l : Int) (_ : solve_precond c v0 v1 a l) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (c v0 v1 a l : Int) (result: Int) (_ : solve_precond c v0 v1 a l) : Prop :=
  result ≥ 1 ∧ computePosition result v0 v1 a l ≥ c ∧ ∀ days, 1 ≤ days ∧ days < result → computePosition days v0 v1 a l < c

theorem solve_spec_satisfied (c v0 v1 a l : Int) (h_precond : solve_precond c v0 v1 a l) :
    solve_postcond c v0 v1 a l (solve c v0 v1 a l h_precond) h_precond := by
  sorry
-- </vc-theorems>