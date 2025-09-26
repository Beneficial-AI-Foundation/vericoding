import Mathlib
-- <vc-preamble>
def ValidInput (a b : Int) : Prop :=
  1 ≤ a ∧ a ≤ 12 ∧ 1 ≤ b ∧ b ≤ 31

def TakahashiCount (a b : Int) : Int :=
  if a > b then a - 1 else a

@[reducible, simp]
def solve_precond (a b : Int) : Prop :=
  ValidInput a b
-- </vc-preamble>

-- <vc-helpers>

-- </vc-helpers>

-- <vc-definitions>
def solve (a b : Int) (h_precond : solve_precond a b) : Int :=
  TakahashiCount a b
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (a b : Int) (result: Int) (h_precond : solve_precond a b) : Prop :=
  result = TakahashiCount a b ∧ (a > b → result = a - 1) ∧ (a ≤ b → result = a)

theorem solve_spec_satisfied (a b : Int) (h_precond : solve_precond a b) :
    solve_postcond a b (solve a b h_precond) h_precond := by
  simp only [solve_postcond, solve]
  constructor
  · -- First goal: TakahashiCount a b = TakahashiCount a b (simplified to True)
    trivial
  constructor  
  · -- Second goal: a > b → TakahashiCount a b = a - 1
    intro h_gt
    simp only [TakahashiCount]
    split
    · rfl
    · next h => contradiction
  · -- Third goal: a ≤ b → TakahashiCount a b = a
    intro h_le
    simp only [TakahashiCount]
    split
    · next h => 
      exfalso
      exact not_lt.mpr h_le h
    · rfl
-- </vc-theorems>
