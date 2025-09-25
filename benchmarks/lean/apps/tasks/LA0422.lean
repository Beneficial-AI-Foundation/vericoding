-- <vc-preamble>
def Abs (x : Int) : Int :=
  if x ≥ 0 then x else -x

def AliceWins (X Y : Int) : Prop :=
  Abs (X - Y) > 1

def BrownWins (X Y : Int) : Prop :=
  Abs (X - Y) ≤ 1

def ValidInput (X Y : Int) : Prop :=
  X ≥ 0 ∧ Y ≥ 0

@[reducible, simp]
def solve_precond (X Y : Int) : Prop :=
  ValidInput X Y
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (X Y : Int) (h_precond : solve_precond X Y) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (X Y : Int) (winner : String) (h_precond : solve_precond X Y) : Prop :=
  (winner = "Alice" ∨ winner = "Brown") ∧
  (winner = "Alice" ↔ AliceWins X Y) ∧
  (winner = "Brown" ↔ BrownWins X Y)

theorem solve_spec_satisfied (X Y : Int) (h_precond : solve_precond X Y) :
    solve_postcond X Y (solve X Y h_precond) h_precond := by
  sorry
-- </vc-theorems>