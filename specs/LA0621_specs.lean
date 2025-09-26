-- <vc-preamble>
def ValidInput (W a b : Int) : Prop :=
  W ≥ 1 ∧ a ≥ 1 ∧ b ≥ 1

def AbsDiff (x y : Int) : Int :=
  if x ≥ y then x - y else y - x

def MinMoveDistance (W a b : Int) : Int :=
  let distance := AbsDiff a b
  if distance ≤ W then 0 else distance - W

def RectanglesConnect (W a b : Int) : Prop :=
  AbsDiff a b ≤ W

@[reducible, simp]
def solve_precond (W a b : Int) : Prop :=
  ValidInput W a b
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (W a b : Int) (h_precond : solve_precond W a b) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (W a b : Int) (result : Int) (h_precond : solve_precond W a b) : Prop :=
  result = MinMoveDistance W a b ∧ 
  result ≥ 0 ∧ 
  (RectanglesConnect W a b ↔ result = 0)

theorem solve_spec_satisfied (W a b : Int) (h_precond : solve_precond W a b) :
    solve_postcond W a b (solve W a b h_precond) h_precond := by
  sorry
-- </vc-theorems>