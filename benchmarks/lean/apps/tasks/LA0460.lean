-- <vc-preamble>
def ValidMatrix (matrix : List (List String)) : Prop :=
  (∀ i, 0 ≤ i ∧ i < matrix.length → matrix[i]!.length = (if matrix.length = 0 then 0 else matrix[0]!.length)) ∧
  (∀ i j, 0 ≤ i ∧ i < matrix.length ∧ 0 ≤ j ∧ j < matrix[i]!.length → matrix[i]![j]! = "0" ∨ matrix[i]![j]! = "1")

def MaxPossibleArea (matrix : List (List String)) : Int :=
  matrix.length * (if matrix.length = 0 then 0 else matrix[0]!.length)

def EmptyMatrix (matrix : List (List String)) : Prop :=
  matrix.length = 0 ∨ matrix[0]!.length = 0

@[reducible, simp]
def solve_precond (matrix : List (List String)) : Prop :=
  ValidMatrix matrix
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (matrix : List (List String)) (h_precond : solve_precond matrix) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (matrix : List (List String)) (result : Int) (h_precond : solve_precond matrix) : Prop :=
  result ≥ 0 ∧ (EmptyMatrix matrix → result = 0) ∧ result ≤ MaxPossibleArea matrix

theorem solve_spec_satisfied (matrix : List (List String)) (h_precond : solve_precond matrix) :
    solve_postcond matrix (solve matrix h_precond) h_precond := by
  sorry
-- </vc-theorems>