-- <vc-preamble>
def ValidInput (t a b : Int) : Prop :=
  t > 0 ∧ a > 0 ∧ b > 0

def ValidOutput (res : String) : Prop :=
  res = "0" ∨ res = "1" ∨ res = "2" ∨ res = "inf"

def InfiniteCase (t a b : Int) : Prop :=
  a = t ∧ a = b ∧ a = 1

def TwoSolutionsCase (t a b : Int) : Prop :=
  a = t ∧ a = b ∧ a ≠ 1

def ZeroSolutionsCase (t a b : Int) : Prop :=
  (t = 2 ∧ a = 3 ∧ b > 10000) ∨
  (a = t ∧ a ≠ b) ∨
  (a ≠ t ∧ (a - b) % (t - a) = 0) ∨
  (a ≠ t ∧ (a - b) % (t - a) ≠ 0 ∧ t = b)

def OneSolutionCase (t a b : Int) : Prop :=
  a ≠ t ∧ (a - b) % (t - a) ≠ 0 ∧ t ≠ b

@[reducible, simp]
def solve_precond (t a b : Int) : Prop :=
  ValidInput t a b ∧ (t ≠ a ∨ a = t)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (t a b : Int) (h_precond : solve_precond t a b) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (t a b : Int) (result : String) (h_precond : solve_precond t a b) : Prop :=
  ValidOutput result ∧
  (InfiniteCase t a b → result = "inf") ∧
  (TwoSolutionsCase t a b → result = "2") ∧
  (ZeroSolutionsCase t a b → result = "0") ∧
  (OneSolutionCase t a b → result = "1")

theorem solve_spec_satisfied (t a b : Int) (h_precond : solve_precond t a b) :
    solve_postcond t a b (solve t a b h_precond) h_precond := by
  sorry
-- </vc-theorems>