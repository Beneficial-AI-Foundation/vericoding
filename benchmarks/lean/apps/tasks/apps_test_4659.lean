-- <vc-preamble>
@[reducible, simp]
def ValidPascalTriangle (triangle : List (List Int)) (numRows : Int) : Prop :=
  triangle.length = numRows ∧
  (numRows = 0 → triangle = []) ∧
  (numRows > 0 → (
    ∀ i, 0 ≤ i ∧ i < triangle.length → triangle[i]!.length = i + 1
  )) ∧
  (numRows > 0 → (
    ∀ i, 0 ≤ i ∧ i < triangle.length → triangle[i]![0]! = 1 ∧ triangle[i]![triangle[i]!.length - 1]! = 1
  )) ∧
  (numRows > 1 → (
    ∀ i, 1 ≤ i ∧ i < triangle.length → 
      ∀ j, 1 ≤ j ∧ j < triangle[i]!.length - 1 → 
        triangle[i]![j]! = triangle[i-1]![j-1]! + triangle[i-1]![j]!
  ))

@[reducible, simp]
def solve_precond (numRows : Int) : Prop :=
  numRows ≥ 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (numRows : Int) (h_precond : solve_precond numRows) : List (List Int) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (numRows : Int) (result : List (List Int)) (h_precond : solve_precond numRows) : Prop :=
  ValidPascalTriangle result numRows

theorem solve_spec_satisfied (numRows : Int) (h_precond : solve_precond numRows) :
    solve_postcond numRows (solve numRows h_precond) h_precond := by
  sorry
-- </vc-theorems>