-- <vc-preamble>
@[reducible, simp]
def strictSorted (arr : Array Int) : Prop :=
  ∀ k l : Nat, k < l → l < arr.size → arr[k]! < arr[l]!

@[reducible, simp]
def mcontained_precond (v : Array Int) (w : Array Int) (n : Nat) (m : Nat) : Prop :=
  n ≤ m ∧ strictSorted v ∧ strictSorted w ∧ v.size ≥ n ∧ w.size ≥ m
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

/- Test cases can be added here -/