import Mathlib
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
-- Helper lemmas for the proof
lemma absDiff_nonneg (x y : Int) : AbsDiff x y ≥ 0 := by
  unfold AbsDiff
  split_ifs <;> omega

lemma absDiff_comm (x y : Int) : AbsDiff x y = AbsDiff y x := by
  unfold AbsDiff
  split_ifs <;> omega

lemma minMoveDistance_nonneg (W a b : Int) (h : W ≥ 1) : MinMoveDistance W a b ≥ 0 := by
  unfold MinMoveDistance
  let distance := AbsDiff a b
  show (if distance ≤ W then 0 else distance - W) ≥ 0
  split_ifs with h1
  · omega
  · have : distance ≥ 0 := absDiff_nonneg a b
    omega

lemma rectanglesConnect_iff_minMoveDistance_zero (W a b : Int) (h : W ≥ 1) :
    RectanglesConnect W a b ↔ MinMoveDistance W a b = 0 := by
  unfold RectanglesConnect MinMoveDistance
  let distance := AbsDiff a b
  show distance ≤ W ↔ (if distance ≤ W then 0 else distance - W) = 0
  constructor
  · intro h_conn
    simp [if_pos h_conn]
  · intro h_zero
    split_ifs at h_zero with h_if
    · exact h_if
    · have : distance ≥ 0 := absDiff_nonneg a b
      omega
-- </vc-helpers>

-- <vc-definitions>
def solve (W a b : Int) (h_precond : solve_precond W a b) : Int :=
  MinMoveDistance W a b
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (W a b : Int) (result : Int) (h_precond : solve_precond W a b) : Prop :=
  result = MinMoveDistance W a b ∧ 
  result ≥ 0 ∧ 
  (RectanglesConnect W a b ↔ result = 0)

theorem solve_spec_satisfied (W a b : Int) (h_precond : solve_precond W a b) :
    solve_postcond W a b (solve W a b h_precond) h_precond := by
  unfold solve_postcond solve
  unfold solve_precond ValidInput at h_precond
  constructor
  · rfl
  constructor
  · exact minMoveDistance_nonneg W a b h_precond.1
  · exact rectanglesConnect_iff_minMoveDistance_zero W a b h_precond.1
-- </vc-theorems>
