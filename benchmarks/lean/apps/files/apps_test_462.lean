-- <vc-preamble>
def ValidInput (x1 x2 x3 : Int) : Prop :=
  1 ≤ x1 ∧ x1 ≤ 100 ∧ 1 ≤ x2 ∧ x2 ≤ 100 ∧ 1 ≤ x3 ∧ x3 ≤ 100 ∧
  x1 ≠ x2 ∧ x1 ≠ x3 ∧ x2 ≠ x3

def MinTotalDistance (x1 x2 x3 : Int) : Int :=
  let max_pos := if x1 ≥ x2 ∧ x1 ≥ x3 then x1
                 else if x2 ≥ x1 ∧ x2 ≥ x3 then x2
                 else x3
  let min_pos := if x1 ≤ x2 ∧ x1 ≤ x3 then x1
                 else if x2 ≤ x1 ∧ x2 ≤ x3 then x2
                 else x3
  max_pos - min_pos

@[reducible, simp]
def solve_precond (x1 x2 x3 : Int) : Prop :=
  ValidInput x1 x2 x3
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (x1 x2 x3 : Int) (h_precond : solve_precond x1 x2 x3) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (x1 x2 x3 : Int) (result : Int) (h_precond : solve_precond x1 x2 x3) : Prop :=
  result = MinTotalDistance x1 x2 x3 ∧ result ≥ 1 ∧ result ≤ 99

theorem solve_spec_satisfied (x1 x2 x3 : Int) (h_precond : solve_precond x1 x2 x3) :
    solve_postcond x1 x2 x3 (solve x1 x2 x3 h_precond) h_precond := by
  sorry
-- </vc-theorems>