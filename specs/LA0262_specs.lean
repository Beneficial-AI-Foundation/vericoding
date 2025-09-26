-- <vc-preamble>
def GetCategory (hp : Int) : Char :=
  let remainder := hp % 4
  if remainder = 1 then 'A'
  else if remainder = 3 then 'B'
  else if remainder = 2 then 'C'
  else 'D'

def ValidInput (n : Int) : Prop :=
  30 ≤ n ∧ n ≤ 100

def ValidOutput (a : Int) (b : Char) : Prop :=
  0 ≤ a ∧ a ≤ 2 ∧ (b = 'A' ∨ b = 'B' ∨ b = 'C' ∨ b = 'D')

def OptimalChoice (n : Int) (a : Int) (b : Char) : Prop :=
  b = GetCategory (n + a) ∧
  ((n % 4 = 1) → (a = 0 ∧ b = 'A')) ∧
  ((n % 4 = 2) → (a = 1 ∧ b = 'B')) ∧
  ((n % 4 = 3) → (a = 2 ∧ b = 'A')) ∧
  ((n % 4 = 0) → (a = 1 ∧ b = 'A'))

@[reducible, simp]
def solve_precond (n : Int) : Prop :=
  ValidInput n
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (h_precond : solve_precond n) : Int × Char :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (result : Int × Char) (h_precond : solve_precond n) : Prop :=
  ValidOutput result.1 result.2 ∧
  OptimalChoice n result.1 result.2 ∧
  (result.2 = 'A' ∨ result.2 = 'B')

theorem solve_spec_satisfied (n : Int) (h_precond : solve_precond n) :
    solve_postcond n (solve n h_precond) h_precond := by
  sorry
-- </vc-theorems>