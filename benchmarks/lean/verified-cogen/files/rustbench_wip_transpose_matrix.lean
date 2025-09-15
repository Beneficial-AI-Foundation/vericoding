-- <vc-preamble>
@[reducible, simp]
def transpose_precond (matrix : Array (Array Int)) : Prop :=
  matrix.size > 0 ∧ 
  (∀ i, i < matrix.size → matrix[i]!.size = matrix[0]!.size) ∧
  (∀ i, i < matrix.size → matrix[i]!.size = matrix.size)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

def main : IO Unit := return ()