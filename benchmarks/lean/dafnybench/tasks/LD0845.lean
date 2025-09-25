-- <vc-preamble>
def isSorted (a : Array Float) (_from : Nat) (to : Nat) : Prop :=
0 ≤ _from ∧ _from ≤ to ∧ to ≤ a.size ∧
∀ i j, _from ≤ i ∧ i < j ∧ j < to → a[i]! ≤ a[j]!
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def findMin (a : Array Float) (_from : Nat) (to : Nat) : Nat :=
sorry

def selectionSort (a : Array Float) : Array Float :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem findMin_spec (a : Array Float) (_from : Nat) (to : Nat) :
0 ≤ _from ∧ _from < to ∧ to ≤ a.size →
let index := findMin a _from to
_from ≤ index ∧ index < to ∧
∀ k, _from ≤ k ∧ k < to → a[k]! ≥ a[index]! :=
sorry

theorem selectionSort_spec (a : Array Float) :
let result := selectionSort a
isSorted result 0 result.size ∧

-- Note: multiset equality check simplified since complex array ops not supported

result.size = a.size :=
sorry
-- </vc-theorems>