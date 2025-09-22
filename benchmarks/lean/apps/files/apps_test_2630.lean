-- <vc-preamble>
def ValidGrid (grid : List (List Int)) : Prop :=
  grid.length > 0 ∧ grid[0]!.length > 0 ∧
  (∀ i, 0 ≤ i ∧ i < grid.length → grid[i]!.length = grid[0]!.length) ∧
  (∀ i j, 0 ≤ i ∧ i < grid.length ∧ 0 ≤ j ∧ j < grid[i]!.length → grid[i]![j]! = 0 ∨ grid[i]![j]! = 1)

def Binomial (n k : Int) : Int :=
  if k > n then 0
  else if k = 0 ∨ k = n then 1
  else if k = 1 then n
  else if n ≥ 1 ∧ k ≥ 1 then Binomial (n-1) (k-1) + Binomial (n-1) k
  else 0
termination_by n.natAbs + k.natAbs

def DPPathCount (grid : List (List Int)) : Int :=
  let m := grid.length
  let n := grid[0]!.length
  if grid[0]![0]! = 1 ∨ grid[m-1]![n-1]! = 1 then 0
  else 
    if m = 1 ∧ n = 1 then 1
    else if m = 1 then 
      if (List.range n).all (fun j => grid[0]![j]! = 0) then 1 else 0
    else if n = 1 then
      if (List.range m).all (fun i => grid[i]![0]! = 0) then 1 else 0
    else if (List.range m).all (fun i => (List.range n).all (fun j => grid[i]![j]! = 0)) then
      Binomial (m + n - 2) (m - 1)
    else
      0

@[reducible, simp]
def solve_precond (obstacleGrid : List (List Int)) : Prop :=
  ValidGrid obstacleGrid
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (obstacleGrid : List (List Int)) (h_precond : solve_precond obstacleGrid) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (obstacleGrid : List (List Int)) (result : Int) (h_precond : solve_precond obstacleGrid) : Prop :=
  result ≥ 0 ∧
  (obstacleGrid[0]![0]! = 1 → result = 0) ∧
  (obstacleGrid[obstacleGrid.length-1]![obstacleGrid[0]!.length-1]! = 1 → result = 0) ∧
  (obstacleGrid.length = 1 ∧ obstacleGrid[0]!.length = 1 → 
   result = (if obstacleGrid[0]![0]! = 0 then 1 else 0)) ∧
  result = DPPathCount obstacleGrid ∧
  ((List.range obstacleGrid.length).all (fun i => (List.range obstacleGrid[0]!.length).all (fun j => obstacleGrid[i]![j]! = 0)) → 
   result = Binomial (obstacleGrid.length + obstacleGrid[0]!.length - 2) (obstacleGrid.length - 1)) ∧
  (obstacleGrid.length = 1 → 
   (result > 0 ↔ (List.range obstacleGrid[0]!.length).all (fun j => obstacleGrid[0]![j]! = 0))) ∧
  (obstacleGrid[0]!.length = 1 → 
   (result > 0 ↔ (List.range obstacleGrid.length).all (fun i => obstacleGrid[i]![0]! = 0)))

theorem solve_spec_satisfied (obstacleGrid : List (List Int)) (h_precond : solve_precond obstacleGrid) :
    solve_postcond obstacleGrid (solve obstacleGrid h_precond) h_precond := by
  sorry
-- </vc-theorems>