-- <vc-preamble>
def sorted_seg (a : Array Int) (i j : Int) : Prop :=
0 ≤ i ∧ i ≤ j ∧ j ≤ a.size ∧
∀ l k : Nat, i ≤ l ∧ l ≤ k ∧ k < j → a[l]! ≤ a[k]!
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def bubbleSorta (a : Array Int) (c f : Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem bubbleSorta_spec (a : Array Int) (c f : Int) :
0 ≤ c ∧ c ≤ f ∧ f ≤ a.size →
let result := bubbleSorta a c f
sorted_seg result c f ∧
result.size = a.size :=
sorry
-- </vc-theorems>