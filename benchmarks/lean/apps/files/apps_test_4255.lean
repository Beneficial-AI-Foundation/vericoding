-- <vc-preamble>
def ValidInput (ab bc ca : Int) : Prop :=
  1 ≤ ab ∧ ab ≤ 100 ∧ 1 ≤ bc ∧ bc ≤ 100 ∧ 1 ≤ ca ∧ ca ≤ 100

def TriangleArea (ab bc : Int) : Int :=
  (ab * bc) / 2

def ValidArea (ab bc area : Int) : Prop :=
  ab ≥ 1 ∧ bc ≥ 1 ∧ area = TriangleArea ab bc ∧ area ≥ 0 ∧ area ≤ 5000

@[reducible, simp]
def solve_precond (ab bc ca : Int) : Prop :=
  ValidInput ab bc ca
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (ab bc ca : Int) (h_precond : solve_precond ab bc ca) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (ab bc ca : Int) (result : String) (h_precond : solve_precond ab bc ca) : Prop :=
  ∃ area, ValidArea ab bc area ∧ result = toString area ++ "\n"

theorem solve_spec_satisfied (ab bc ca : Int) (h_precond : solve_precond ab bc ca) :
    solve_postcond ab bc ca (solve ab bc ca h_precond) h_precond := by
  sorry
-- </vc-theorems>