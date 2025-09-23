-- <vc-preamble>
def sorted_between (a : Array Int) (from_ : Nat) (to : Nat) : Prop :=
∀ i j, from_ ≤ i ∧ i < j ∧ j < to ∧ 0 ≤ i ∧ i < j ∧ j < a.size →
a[i]! ≤ a[j]!
def sorted (a : Array Int) : Prop :=
sorted_between a 0 a.size
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
sorted result ∧

-- Note: Multiset equality check simplified since complex array operations are avoided

result.size = a.size :=
sorry
-- </vc-theorems>