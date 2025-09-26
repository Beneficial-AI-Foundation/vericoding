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

-- </vc-helpers>

-- <vc-definitions>
def solve (a b c d : Int) (h_precond : solve_precond a b c d) : Int :=
  if a ≤ b then
    b
  else if c ≤ d then
    -1
  else
    CalculateWakeTime a b c d
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (a b c d : Int) (result : Int) (h_precond : solve_precond a b c d) : Prop :=
  (FirstAlarmSufficient a b → result = b) ∧
  (NeverWakes a b c d → result = -1) ∧
  (EventuallyWakes a b c d → result = CalculateWakeTime a b c d)

theorem solve_spec_satisfied (a b c d : Int) (h_precond : solve_precond a b c d) :
    solve_postcond a b c d (solve a b c d h_precond) h_precond := by
  unfold solve_postcond FirstAlarmSufficient NeverWakes EventuallyWakes solve
  constructor
  · -- Case 1: FirstAlarmSufficient (a ≤ b)
    intro h_fas
    simp [h_fas]
  · constructor
    · -- Case 2: NeverWakes (a > b ∧ c ≤ d)
      intro h_nw
      have not_a_le_b : ¬(a ≤ b) := by linarith [h_nw.1]
      simp [not_a_le_b, h_nw.2]
    · -- Case 3: EventuallyWakes (a > b ∧ c > d)
      intro h_ew
      have not_a_le_b : ¬(a ≤ b) := by linarith [h_ew.1]
      have not_c_le_d : ¬(c ≤ d) := by linarith [h_ew.2]
      simp [not_a_le_b, not_c_le_d]
-- </vc-theorems>
