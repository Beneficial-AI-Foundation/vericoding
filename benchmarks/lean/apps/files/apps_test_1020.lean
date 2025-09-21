-- <vc-preamble>
def ValidInput (w h k : Int) : Prop :=
  w ≥ 3 ∧ h ≥ 3 ∧ w ≤ 100 ∧ h ≤ 100 ∧ 
  k ≥ 1 ∧ k ≤ ((if w ≤ h then w else h) + 1) / 4 ∧
  w - 4 * k ≥ 3 ∧ h - 4 * k ≥ 3

def perimeter (w h : Int) : Int :=
  w * 2 + (h - 2) * 2

def computeSum (w h : Int) : Nat → Int
  | 0 => 0
  | k + 1 => perimeter w h + computeSum (w - 4) (h - 4) k

@[reducible, simp]
def solve_precond (w h k : Int) : Prop :=
  ValidInput w h k
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (w h k : Int) (h_precond : solve_precond w h k) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (w h k : Int) (result : Int) (h_precond : solve_precond w h k) : Prop :=
  result = computeSum w h k.natAbs

theorem solve_spec_satisfied (w h k : Int) (h_precond : solve_precond w h k) :
    solve_postcond w h k (solve w h k h_precond) h_precond := by
  sorry
-- </vc-theorems>