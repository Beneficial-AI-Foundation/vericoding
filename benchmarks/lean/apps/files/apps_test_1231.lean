-- <vc-preamble>
def ValidInput (a b : Int) : Prop :=
  0 ≤ a ∧ a ≤ 100 ∧ 0 ≤ b ∧ b ≤ 100

def ValidOutput (result : String) : Prop :=
  result = "YES" ∨ result = "NO"

def abs (x : Int) : Int :=
  if x ≥ 0 then x else -x

def IntervalExists (a b : Int) : Prop :=
  abs (a - b) ≤ 1 ∧ a + b > 0

@[reducible, simp]
def solve_precond (a b : Int) : Prop :=
  ValidInput a b
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (a b : Int) (h_precond : solve_precond a b) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (a b : Int) (result : String) (h_precond : solve_precond a b) : Prop :=
  ValidOutput result ∧ (result = "YES" ↔ IntervalExists a b)

theorem solve_spec_satisfied (a b : Int) (h_precond : solve_precond a b) :
    solve_postcond a b (solve a b h_precond) h_precond := by
  sorry
-- </vc-theorems>