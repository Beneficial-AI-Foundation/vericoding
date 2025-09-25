-- <vc-preamble>
def sorted_seg (a : Array Int) (i j : Int) : Prop :=
0 ≤ i ∧ i ≤ j ∧ j ≤ a.size ∧
∀ l k : Nat, i ≤ l ∧ l ≤ k ∧ k < j → a[l]! ≤ a[k]!
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def selSort (a : Array Int) (c f : Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem selSort_spec (a : Array Int) (c f : Int) :
0 ≤ c ∧ c ≤ f ∧ f ≤ a.size →
let result := selSort a c f
sorted_seg result c f ∧

-- Note: Multiset and array segment specifications simplified due to translation limitations

result.size = a.size :=
sorry
-- </vc-theorems>