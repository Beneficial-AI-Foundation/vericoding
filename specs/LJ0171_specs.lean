-- <vc-preamble>
@[reducible, simp]
def transpose_precond (matrix : Array (Array Int)) : Prop :=
  matrix.size > 0 ∧ 
  (∀ i, i < matrix.size → matrix[i]!.size = matrix[0]!.size) ∧
  (∀ i, i < matrix.size → matrix[i]!.size = matrix.size)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def transpose (matrix : Array (Array Int)) (h_precond : transpose_precond matrix) : Array (Array Int) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def transpose_postcond (matrix : Array (Array Int)) (result : Array (Array Int)) (h_precond : transpose_precond matrix) : Prop :=
  result.size = matrix[0]!.size ∧
  (∀ i, i < result.size → result[i]!.size = matrix.size) ∧
  (∀ i j, i < result.size → j < result[i]!.size → result[i]![j]! = matrix[j]![i]!)

theorem transpose_spec_satisfied (matrix : Array (Array Int)) (h_precond : transpose_precond matrix) :
    transpose_postcond matrix (transpose matrix h_precond) h_precond := by
  sorry
-- </vc-theorems>