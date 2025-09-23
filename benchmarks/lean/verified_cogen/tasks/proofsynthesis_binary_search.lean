-- <vc-preamble>
@[reducible, simp]
def binarySearch_precond (v : Array Nat) (k : Nat) : Prop :=
  (∀ i j, i ≤ j → j < v.size → v[i]! ≤ v[j]!) ∧ (∃ i, i < v.size ∧ k = v[i]!)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def binarySearch (v : Array Nat) (k : Nat) (h_precond : binarySearch_precond v k) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def binarySearch_postcond (v : Array Nat) (k : Nat) (result : Nat) (h_precond : binarySearch_precond v k) : Prop :=
  result < v.size ∧ k = v[result]!

theorem binarySearch_spec_satisfied (v : Array Nat) (k : Nat) (h_precond : binarySearch_precond v k) :
    binarySearch_postcond v k (binarySearch v k h_precond) h_precond := by
  sorry
-- </vc-theorems>