import Mathlib
-- <vc-preamble>
def ValidInput (y1 y2 y_w x_b y_b r : Int) : Prop :=
  y1 < y2 ∧ y2 < y_w ∧
  y_b + r < y_w ∧
  2 * r < y2 - y1 ∧
  x_b > 0 ∧ y_b > 0 ∧ r > 0 ∧
  2 * (y_w - r) - y1 - y_b - r ≠ 0

def ComputeW (y_w r : Int) : Int :=
  y_w - r

def ComputeNewY1 (y_w r y1 y_b : Int) : Int :=
  2 * (y_w - r) - y1 - y_b - r

def ComputeNewY2 (y_w r y2 y_b : Int) : Int :=
  2 * (y_w - r) - y2 - y_b

def ComputeLeftSide (x_b new_y1 new_y2 : Int) : Int :=
  x_b * x_b * (new_y2 - new_y1) * (new_y2 - new_y1)

def ComputeRightSide (x_b new_y1 r : Int) : Int :=
  (new_y1 * new_y1 + x_b * x_b) * r * r

def IsImpossible (y1 y2 y_w x_b y_b r : Int) : Prop :=
  let new_y1 := ComputeNewY1 y_w r y1 y_b
  let new_y2 := ComputeNewY2 y_w r y2 y_b
  let left_side := ComputeLeftSide x_b new_y1 new_y2
  let right_side := ComputeRightSide x_b new_y1 r
  left_side ≤ right_side

def ComputeSolution (y1 y2 y_w x_b y_b r : Int) : Float :=
  let w := ComputeW y_w r
  let new_y1 := ComputeNewY1 y_w r y1 y_b
  Float.ofInt x_b * Float.ofInt (new_y1 + y_b - w) / Float.ofInt new_y1

@[reducible, simp]
def solve_precond (y1 y2 y_w x_b y_b r : Int) : Prop :=
  ValidInput y1 y2 y_w x_b y_b r
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Decidable instance for IsImpossible
instance IsImpossible_decidable (y1 y2 y_w x_b y_b r : Int) : 
  Decidable (IsImpossible y1 y2 y_w x_b y_b r) := by
  unfold IsImpossible
  infer_instance

lemma ValidInput_implies_new_y1_nonzero (y1 y2 y_w x_b y_b r : Int) 
    (h : ValidInput y1 y2 y_w x_b y_b r) : 
    ComputeNewY1 y_w r y1 y_b ≠ 0 := by
  unfold ValidInput ComputeNewY1 at *
  omega
-- </vc-helpers>

-- <vc-definitions>
def solve (y1 y2 y_w x_b y_b r : Int) (h_precond : solve_precond y1 y2 y_w x_b y_b r) : Float :=
  if IsImpossible y1 y2 y_w x_b y_b r then 
    -1.0 
  else 
    ComputeSolution y1 y2 y_w x_b y_b r
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (y1 y2 y_w x_b y_b r : Int) (result : Float) (h_precond : solve_precond y1 y2 y_w x_b y_b r) : Prop :=
  (IsImpossible y1 y2 y_w x_b y_b r → result = -1.0) ∧
  (¬IsImpossible y1 y2 y_w x_b y_b r → result = ComputeSolution y1 y2 y_w x_b y_b r)

theorem solve_spec_satisfied (y1 y2 y_w x_b y_b r : Int) (h_precond : solve_precond y1 y2 y_w x_b y_b r) :
    solve_postcond y1 y2 y_w x_b y_b r (solve y1 y2 y_w x_b y_b r h_precond) h_precond := by
  unfold solve_postcond solve
  constructor
  · intro h_impossible
    simp [h_impossible]
  · intro h_not_impossible  
    simp [h_not_impossible]
-- </vc-theorems>
