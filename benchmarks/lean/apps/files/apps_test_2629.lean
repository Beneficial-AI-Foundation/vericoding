-- <vc-preamble>
def customMin (a b : Int) : Int :=
  if a ≤ b then a else b

def SpiralOrder (row col n : Int) : Int :=
  let layer := customMin (customMin row col) (customMin (n-1-row) (n-1-col))
  let layerStart := 4 * layer * (n - layer - 1) + layer
  if row = layer then
    layerStart + (col - layer)
  else if col = n - 1 - layer then
    layerStart + (n - 2 * layer - 1) + (row - layer)
  else if row = n - 1 - layer then
    layerStart + 2 * (n - 2 * layer - 1) + (n - 1 - layer - col)
  else
    layerStart + 3 * (n - 2 * layer - 1) + (n - 1 - layer - row)

def ValidInput (n : Int) : Prop :=
  n ≥ 1

def ValidSpiralMatrix (matrix : List (List Int)) (n : Int) : Prop :=
  matrix.length = n.natAbs ∧ (∀ row ∈ matrix, row.length = n.natAbs) ∧
  (∀ i j : Nat, i < n.natAbs ∧ j < n.natAbs → matrix[i]![j]! = SpiralOrder i j n + 1)

@[reducible, simp]
def solve_precond (n : Int) : Prop :=
  ValidInput n
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (h_precond : solve_precond n) : List (List Int) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (result : List (List Int)) (h_precond : solve_precond n) : Prop :=
  ValidSpiralMatrix result n ∧
  result.length = n.natAbs ∧ (∀ row ∈ result, row.length = n.natAbs) ∧
  (∀ i j : Nat, i < n.natAbs ∧ j < n.natAbs → 1 ≤ result[i]![j]! ∧ result[i]![j]! ≤ n * n) ∧
  (∀ v, 1 ≤ v ∧ v ≤ n * n → ∃ i j : Nat, i < n.natAbs ∧ j < n.natAbs ∧ result[i]![j]! = v)

theorem solve_spec_satisfied (n : Int) (h_precond : solve_precond n) :
    solve_postcond n (solve n h_precond) h_precond := by
  sorry
-- </vc-theorems>