import Mathlib
-- <vc-preamble>
def ValidInput (l1 r1 l2 r2 k : Int) : Prop :=
  l1 ≤ r1 ∧ l2 ≤ r2

def IntersectionLeft (l1 l2 : Int) : Int :=
  if l1 > l2 then l1 else l2

def IntersectionRight (r1 r2 : Int) : Int :=
  if r1 < r2 then r1 else r2

def IntersectionSize (l1 r1 l2 r2 : Int) : Int :=
  let left := IntersectionLeft l1 l2
  let right := IntersectionRight r1 r2
  if right - left + 1 > 0 then right - left + 1 else 0

def KInIntersection (l1 r1 l2 r2 k : Int) : Bool :=
  let left := IntersectionLeft l1 l2
  let right := IntersectionRight r1 r2
  left ≤ k && k ≤ right

def ExpectedResult (l1 r1 l2 r2 k : Int) : Int :=
  let intersection_size := IntersectionSize l1 r1 l2 r2
  if KInIntersection l1 r1 l2 r2 k then
    if intersection_size - 1 > 0 then intersection_size - 1 else 0
  else
    intersection_size

@[reducible, simp]
def solve_precond (l1 r1 l2 r2 k : Int) : Prop :=
  ValidInput l1 r1 l2 r2 k
-- </vc-preamble>

-- <vc-helpers>

-- </vc-helpers>

-- <vc-definitions>
def solve (l1 r1 l2 r2 k : Int) (h_precond : solve_precond l1 r1 l2 r2 k) : Int :=
  ExpectedResult l1 r1 l2 r2 k
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (l1 r1 l2 r2 k : Int) (result : Int) (h_precond : solve_precond l1 r1 l2 r2 k) : Prop :=
  result = ExpectedResult l1 r1 l2 r2 k ∧ result ≥ 0

theorem solve_spec_satisfied (l1 r1 l2 r2 k : Int) (h_precond : solve_precond l1 r1 l2 r2 k) :
    solve_postcond l1 r1 l2 r2 k (solve l1 r1 l2 r2 k h_precond) h_precond := by
  simp [solve, solve_postcond, ExpectedResult, IntersectionSize, KInIntersection, IntersectionLeft, IntersectionRight]
  split_ifs
  all_goals linarith
-- </vc-theorems>
