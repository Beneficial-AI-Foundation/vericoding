-- <vc-preamble>
def isSorted (a : Array Int) : Prop :=
∀ i j, 0 ≤ i → i < j → j < a.size → a[i]! ≤ a[j]!
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def binarySearch (a : Array Int) (x : Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem binarySearch_spec (a : Array Int) (x : Int) :
isSorted a →
let index := binarySearch a x
(-1 ≤ index ∧ index < a.size ∧
(index ≠ -1 → a[index.toNat]! = x) ∧
(index = -1 → ∀ i:Nat, 0 ≤ i → i < a.size → a[i]! ≠ x)) :=
sorry
-- </vc-theorems>