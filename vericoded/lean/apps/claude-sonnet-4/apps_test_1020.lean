import Mathlib
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
-- LLM HELPER: Convert Int to Nat safely for computeSum
def intToNat (k : Int) : Nat :=
  if k ≥ 0 then k.natAbs else 0

-- LLM HELPER: Lemma about natAbs for non-negative integers
lemma natAbs_of_nonneg {k : Int} (hk : k ≥ 0) : k.natAbs = intToNat k := by
  simp [intToNat, hk]
-- </vc-helpers>

-- <vc-definitions>
def solve (w h k : Int) (h_precond : solve_precond w h k) : Int :=
  computeSum w h k.natAbs
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (w h k : Int) (result : Int) (h_precond : solve_precond w h k) : Prop :=
  result = computeSum w h k.natAbs

theorem solve_spec_satisfied (w h k : Int) (h_precond : solve_precond w h k) :
    solve_postcond w h k (solve w h k h_precond) h_precond := by
  unfold solve_postcond solve
  rfl
-- </vc-theorems>
