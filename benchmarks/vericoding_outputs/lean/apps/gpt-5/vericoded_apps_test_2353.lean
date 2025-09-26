import Mathlib
-- <vc-preamble>
def ValidInput (a b c d : Int) : Prop :=
  a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ d ≥ 0

def FirstAlarmSufficient (a b : Int) : Prop :=
  a ≤ b

def NeverWakes (a b c d : Int) : Prop :=
  a > b ∧ c ≤ d

def EventuallyWakes (a b c d : Int) : Prop :=
  a > b ∧ c > d

def CalculateWakeTime (a b c d : Int) : Int :=
  let remaining := a - b
  let cycles := (remaining - 1) / (c - d) + 1
  b + c * cycles

@[reducible, simp]
def solve_precond (a b c d : Int) : Prop :=
  ValidInput a b c d
-- </vc-preamble>

-- <vc-helpers>
-- no helpers needed
-- </vc-helpers>

-- <vc-definitions>
def solve (a b c d : Int) (h_precond : solve_precond a b c d) : Int :=
  if h₁ : a ≤ b then b else if h₂ : c ≤ d then -1 else CalculateWakeTime a b c d
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (a b c d : Int) (result : Int) (h_precond : solve_precond a b c d) : Prop :=
  (FirstAlarmSufficient a b → result = b) ∧
  (NeverWakes a b c d → result = -1) ∧
  (EventuallyWakes a b c d → result = CalculateWakeTime a b c d)

theorem solve_spec_satisfied (a b c d : Int) (h_precond : solve_precond a b c d) :
    solve_postcond a b c d (solve a b c d h_precond) h_precond := by
  classical
  unfold solve_postcond
  by_cases h₁ : a ≤ b
  · constructor
    · intro _; simp [solve, h₁]
    · constructor
      · intro hNW; exact False.elim ((not_le.mpr hNW.1) h₁)
      · intro hEW; exact False.elim ((not_le.mpr hEW.1) h₁)
  · by_cases h₂ : c ≤ d
    · constructor
      · intro hFab; exact False.elim (h₁ hFab)
      · constructor
        · intro _; simp [solve, h₁, h₂]
        · intro hEW; exact False.elim ((not_le.mpr hEW.2) h₂)
    · constructor
      · intro hFab; exact False.elim (h₁ hFab)
      · constructor
        · intro hNW; exact False.elim (h₂ hNW.2)
        · intro _; simp [solve, h₁, h₂]
-- </vc-theorems>
