-- <vc-preamble>
def isSorted (a : Array Int) : Prop :=
∀ i j : Nat, i ≤ j ∧ j < a.size → a[i]! ≤ a[j]!
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def binSearch (a : Array Int) (K : Int) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem binSearch_spec (a : Array Int) (K : Int) :
isSorted a →
binSearch a K = (∃ i : Nat, i < a.size ∧ a[i]! = K) :=
sorry
-- </vc-theorems>