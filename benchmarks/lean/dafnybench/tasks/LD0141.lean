-- <vc-preamble>
def sorted_seg (a : Array Int) (i j : Int) : Prop :=
∀ l k, i ≤ l ∧ l ≤ k ∧ k ≤ j → a[l.toNat]! ≤ a[k.toNat]!
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def InsertionSort (a : Array Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem InsertionSort_spec (a : Array Int) :
let result := InsertionSort a
sorted_seg result 0 (result.size - 1) :=
sorry
-- </vc-theorems>