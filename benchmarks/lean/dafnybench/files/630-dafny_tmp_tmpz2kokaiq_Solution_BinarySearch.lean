-- <vc-preamble>
def sorted (a : Array Int) : Prop :=
∀ i j , 0 ≤ i ∧ i < j ∧ j < a.size → a[i]! ≤ a[j]!
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def BinarySearch (a : Array Int) (x : Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem BinarySearch_spec (a : Array Int) (x : Int) :
sorted a →
let index := BinarySearch a x
(0 ≤ index ∧ index < a.size → a[index.toNat]! = x) ∧
(index = -1 → ∀ i , 0 ≤ i ∧ i < a.size → a[i]! ≠ x) :=
sorry
-- </vc-theorems>