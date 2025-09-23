-- <vc-preamble>
def ValidPath (path : List (Nat × Nat)) (m n : Nat) : Prop :=
  path.length ≥ 1 ∧
  path.head? = some (0, 0) ∧
  path.getLast? = some (m-1, n-1) ∧
  (∀ i, i < path.length → (path[i]!).1 < m ∧ (path[i]!).2 < n) ∧
  ∀ i, i < path.length - 1 → 
      ((path[i+1]!).1 = (path[i]!).1 ∧ (path[i+1]!).2 = (path[i]!).2 + 1) ∨
      ((path[i+1]!).1 = (path[i]!).1 + 1 ∧ (path[i+1]!).2 = (path[i]!).2)

def PathSum (path : List (Nat × Nat)) (grid : Array (Array Int)) : Int :=
  match path with
  | [] => 0
  | h :: t => grid[h.1]![h.2]! + PathSum t grid

def ValidInput (grid : Array (Array Int)) : Prop :=
  grid.size > 0 ∧ grid[0]!.size > 0 ∧
  ∀ i j, i < grid.size ∧ j < grid[0]!.size → grid[i]![j]! ≥ 0

@[reducible, simp]
def solve_precond (grid : Array (Array Int)) : Prop :=
  ValidInput grid
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (grid : Array (Array Int)) (h_precond : solve_precond grid) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (grid : Array (Array Int)) (result : Int) (h_precond : solve_precond grid) : Prop :=
  result ≥ 0 ∧ (grid.size = 1 ∧ grid[0]!.size = 1 → result = grid[0]![0]!)

theorem solve_spec_satisfied (grid : Array (Array Int)) (h_precond : solve_precond grid) :
    solve_postcond grid (solve grid h_precond) h_precond := by
  sorry
-- </vc-theorems>