-- <vc-preamble>
def sorted (a : Array Int) (start : Nat) (end_ : Nat) : Prop :=
a.size > 0 ∧
0 ≤ start ∧ start ≤ end_ ∧ end_ ≤ a.size ∧
∀ j k, start ≤ j ∧ j < k ∧ k < end_ → a[j]! ≤ a[k]!
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def InsertionSort (a : Array Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem InsertionSort_spec (a : Array Int) :
a.size > 1 →
sorted (InsertionSort a) 0 (InsertionSort a).size :=
sorry
-- </vc-theorems>