-- <vc-preamble>
/- Recursive sum function for array segments -/
def sum (a : Array Int) (s : Int) (t : Int) : Int :=
  if s < 0 ∨ s ≥ t ∨ t > a.size then
    0
  else
    a[t.toNat - 1]! + sum a s (t - 1)
termination_by (t - s).toNat

@[reducible, simp]
def maxSegmentSum_precond (a : Array Int) (s : Nat) (t : Nat) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def maxSegmentSum (a : Array Int) (s : Nat) (t : Nat) (h_precond : maxSegmentSum_precond a s t) : Nat × Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def maxSegmentSum_postcond (a : Array Int) (s : Nat) (t : Nat) (result : Nat × Nat) (h_precond : maxSegmentSum_precond a s t) : Prop :=
  let (i, j) := result
  (0 ≤ i ∧ i ≤ j ∧ j ≤ a.size) ∧ 
  (∀ k l : Int, 0 ≤ k ∧ k ≤ l ∧ l ≤ a.size → sum a k l ≤ sum a i j)

theorem maxSegmentSum_spec_satisfied (a : Array Int) (s : Nat) (t : Nat) (h_precond : maxSegmentSum_precond a s t) :
    maxSegmentSum_postcond a s t (maxSegmentSum a s t h_precond) h_precond := by
  sorry
-- </vc-theorems>