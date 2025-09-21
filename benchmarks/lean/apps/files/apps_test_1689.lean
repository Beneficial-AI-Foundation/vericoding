-- <vc-preamble>
def ValidInput (n : Int) (rows : List String) : Prop :=
  n ≥ 0 ∧ rows.length = n.natAbs ∧ ∀ i, 0 ≤ i ∧ i < rows.length → (rows[i]!).length = 5

def HasAdjacentEmptySeats (rows : List String) : Prop :=
  ∃ i, 0 ≤ i ∧ i < rows.length ∧ 
    ((rows[i]!).length ≥ 2 ∧ (rows[i]!).data[0]! = 'O' ∧ (rows[i]!).data[1]! = 'O') ∨
    ((rows[i]!).length ≥ 5 ∧ (rows[i]!).data[3]! = 'O' ∧ (rows[i]!).data[4]! = 'O')

def NoAdjacentEmptySeats (rows : List String) : Prop :=
  ∀ i, 0 ≤ i ∧ i < rows.length → 
    ¬((rows[i]!).length ≥ 2 ∧ (rows[i]!).data[0]! = 'O' ∧ (rows[i]!).data[1]! = 'O') ∧
    ¬((rows[i]!).length ≥ 5 ∧ (rows[i]!).data[3]! = 'O' ∧ (rows[i]!).data[4]! = 'O')

def ValidSolution (result : String) : Prop :=
  result ≠ "NO" → result.length ≥ 4

@[reducible, simp]
def solve_precond (n : Int) (rows : List String) : Prop :=
  ValidInput n rows
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (rows : List String) (h_precond : solve_precond n rows) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (rows : List String) (result : String) (h_precond : solve_precond n rows) : Prop :=
  (result = "NO" ∨ result.length ≥ 4) ∧
  (result = "NO" → NoAdjacentEmptySeats rows) ∧
  (result ≠ "NO" → HasAdjacentEmptySeats rows) ∧
  ValidSolution result

theorem solve_spec_satisfied (n : Int) (rows : List String) (h_precond : solve_precond n rows) :
    solve_postcond n rows (solve n rows h_precond) h_precond := by
  sorry
-- </vc-theorems>