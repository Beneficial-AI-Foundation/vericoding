-- <vc-preamble>
def ValidInput (m b : Int) : Prop :=
  1 ≤ m ∧ m ≤ 1000 ∧ 1 ≤ b ∧ b ≤ 10000

def f (x y : Int) : Int :=
  (x * (x + 1) * (y + 1) + y * (y + 1) * (x + 1)) / 2

def ValidRectangleCorner (k m b : Int) : Prop :=
  0 ≤ k ∧ b - k ≥ 0

def RectangleValue (k m b : Int) : Int :=
  f (k * m) (b - k)

@[reducible, simp]
def solve_precond (m b : Int) : Prop :=
  ValidInput m b
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (m b : Int) (h_precond : solve_precond m b) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (m b : Int) (result : Int) (h_precond : solve_precond m b) : Prop :=
  result ≥ -1 ∧
  (∀ k, ValidRectangleCorner k m b → result ≥ RectangleValue k m b) ∧
  (∃ k, ValidRectangleCorner k m b ∧ result = RectangleValue k m b)

theorem solve_spec_satisfied (m b : Int) (h_precond : solve_precond m b) :
    solve_postcond m b (solve m b h_precond) h_precond := by
  sorry
-- </vc-theorems>