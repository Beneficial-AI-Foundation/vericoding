-- <vc-preamble>

def ValidInput (n m k : Int) (grid : List String) : Prop :=
  n > 0 ∧ m > 0 ∧ k ≥ 0 ∧
  grid.length = n.natAbs ∧
  (∀ i, 0 ≤ i ∧ i < n → grid[i.natAbs]!.length = m.natAbs) ∧
  (∃ i j, 0 ≤ i ∧ i < n ∧ 0 ≤ j ∧ j < m ∧ grid[i.natAbs]!.toList[j.natAbs]! = 'X') ∧
  (∀ i, 0 ≤ i ∧ i < n → ∀ c, c ∈ grid[i.natAbs]!.toList → c = '.' ∨ c = '*' ∨ c = 'X') ∧
  True

def GetNextPosition (x y : Int) (move : Char) : Int × Int :=
  match move with
  | 'D' => (x + 1, y)
  | 'L' => (x, y - 1)
  | 'R' => (x, y + 1)
  | 'U' => (x - 1, y)
  | _ => (x, y)

def SimulatePath (startX startY : Int) (path : String) : Int × Int :=
  path.toList.foldl (fun pos c => GetNextPosition pos.1 pos.2 c) (startX, startY)

def ValidPath (startX startY : Int) (path : String) (grid : List String) (n m : Int) : Prop :=
  ∀ i, 0 ≤ i ∧ i ≤ path.length →
    let pos := SimulatePath startX startY (path.take i)
    0 ≤ pos.1 ∧ pos.1 < n ∧ 0 ≤ pos.2 ∧ pos.2 < m ∧
    pos.1.natAbs < grid.length ∧ pos.2.natAbs < grid[pos.1.natAbs]!.length ∧
    grid[pos.1.natAbs]!.toList[pos.2.natAbs]! ≠ '*'

def PathReturnsToStart (startX startY : Int) (path : String) : Prop :=
  let finalPos := SimulatePath startX startY path
  finalPos.1 = startX ∧ finalPos.2 = startY

def ValidDirections (path : String) : Prop :=
  ∀ c, c ∈ path.toList → c = 'D' ∨ c = 'L' ∨ c = 'R' ∨ c = 'U'

@[reducible, simp]
def solve_precond (n m k : Int) (grid : List String) : Prop :=
  ValidInput n m k grid
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n m k : Int) (grid : List String) (h_precond : solve_precond n m k grid) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n m k : Int) (grid : List String) (result : String) (h_precond : solve_precond n m k grid) : Prop :=
  (k % 2 = 1 → result = "IMPOSSIBLE") ∧
  (k % 2 = 0 → (result = "IMPOSSIBLE" ∨ (result.length = k.natAbs ∧ ValidDirections result))) ∧
  (result ≠ "IMPOSSIBLE" → result.length = k.natAbs) ∧
  (result ≠ "IMPOSSIBLE" → 
    ∃ startX startY, 0 ≤ startX ∧ startX < n ∧ 0 ≤ startY ∧ startY < m ∧
    grid[startX.natAbs]!.toList[startY.natAbs]! = 'X' ∧
    PathReturnsToStart startX startY result) ∧
  (result ≠ "IMPOSSIBLE" →
    ∃ startX startY, 0 ≤ startX ∧ startX < n ∧ 0 ≤ startY ∧ startY < m ∧
    grid[startX.natAbs]!.toList[startY.natAbs]! = 'X' ∧
    ValidPath startX startY result grid n m)

theorem solve_spec_satisfied (n m k : Int) (grid : List String) (h_precond : solve_precond n m k grid) :
    solve_postcond n m k grid (solve n m k grid h_precond) h_precond := by
  sorry
-- </vc-theorems>