-- <vc-preamble>
@[reducible, simp]
def binarySearch_precond (v : Array Nat) (k : Nat) : Prop :=
  (∀ i j, i ≤ j → j < v.size → v[i]! ≤ v[j]!) ∧ (∃ i, i < v.size ∧ k = v[i]!)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

#check binarySearch
#check binarySearch_precond
#check binarySearch_postcond