-- <vc-preamble>
def sorted (a : Array Int) : Prop :=
∀ j k, 0 ≤ j → j < k → k < a.size → a[j]! ≤ a[k]!
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def BinarySearch (a : Array Int) (value : Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem BinarySearch_spec (a : Array Int) (value : Int) :
sorted a →
let index := BinarySearch a value
(0 ≤ index → index < a.size ∧ a[index.toNat]! = value) ∧
(index < 0 → ∀ k, 0 ≤ k → k < a.size → a[k]! ≠ value) :=
sorry
-- </vc-theorems>