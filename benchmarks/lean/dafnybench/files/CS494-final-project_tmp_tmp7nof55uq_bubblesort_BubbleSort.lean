-- <vc-preamble>
def sorted (a : Array Int) (_from : Int) (to : Int) : Prop :=
a.size > 0 ∧
0 ≤ _from ∧ _from ≤ to ∧ to ≤ a.size ∧
∀ x y, _from ≤ x ∧ x < y ∧ y < to → a[x.toNat]! ≤ a[y.toNat]!
def pivot (a : Array Int) (to : Int) (pvt : Int) : Prop :=
a.size > 0 ∧
0 ≤ pvt ∧ pvt < to ∧ to ≤ a.size ∧
∀ x y, 0 ≤ x ∧ x < pvt ∧ pvt < y ∧ y < to → a[x.toNat]! ≤ a[y.toNat]!
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def BubbleSort (a : Array Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem BubbleSort_spec (a : Array Int) :
a.size > 0 →
let result := BubbleSort a
sorted result 0 result.size ∧
result.size = a.size :=
sorry
-- </vc-theorems>