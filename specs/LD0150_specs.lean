-- <vc-preamble>
def sorted (a : Array Int) (l : Int) (u : Int) : Prop :=
∀ i j, 0 ≤ l ∧ l ≤ i ∧ i ≤ j ∧ j ≤ u ∧ u < a.size → a[i.toNat]! ≤ a[j.toNat]!
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def BinarySearch (a : Array Int) (key : Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem BinarySearch_spec (a : Array Int) (key : Int) :
sorted a 0 (a.size - 1) →
let index := BinarySearch a key
(index ≥ 0 → index < a.size ∧ a[index.toNat]! = key) ∧
(index < 0 → ∀ k, 0 ≤ k ∧ k < a.size → a[k]! ≠ key) :=
sorry
-- </vc-theorems>