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
-- Helper lemmas for conditional reasoning
lemma takahashi_count_gt (a b : Int) (h : a > b) : TakahashiCount a b = a - 1 := by
  simp [TakahashiCount, h]

lemma takahashi_count_le (a b : Int) (h : a ≤ b) : TakahashiCount a b = a := by
  simp [TakahashiCount, h]
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
  unfold solve_postcond solve TakahashiCount
  constructor
  · rfl
  constructor
  · intro h_gt
    simp [h_gt]
  · intro h_le
    simp [h_le]
-- </vc-theorems>
