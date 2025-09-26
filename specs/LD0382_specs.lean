-- <vc-preamble>
def sorted (a : Array Int) (from_ : Nat) (to : Nat) : Prop :=
∀ u v, from_ ≤ u ∧ u < v ∧ v < to → a[u]! ≤ a[v]!
def pivot (a : Array Int) (to : Nat) (pvt : Nat) : Prop :=
∀ u v, 0 ≤ u ∧ u < pvt ∧ pvt < v ∧ v < to → a[u]! ≤ a[v]!
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def bubbleSort (a : Array Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem bubbleSort_spec (a : Array Int) :
a.size > 0 →
let result := bubbleSort a
sorted result 0 result.size ∧

-- Note: Multiset equality is simplified to size equality for basic spec

result.size = a.size :=
sorry
-- </vc-theorems>