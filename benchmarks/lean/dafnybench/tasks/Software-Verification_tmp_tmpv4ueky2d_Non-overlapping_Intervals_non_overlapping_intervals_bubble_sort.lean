-- <vc-preamble>
structure Array2D (α : Type) where
data : Array (Array α)
dim1_eq_2 : ∀ arr ∈ data, arr.size = 2
def sorted (a : Array2D Int) (l u : Int) : Prop :=
∀ i j:Nat, 0 ≤ l → l ≤ i → i ≤ j → j ≤ u → u < a.data.size →
(a.data[i]!)[1]! ≤ (a.data[j]!)[1]!
def partitioned (a : Array2D Int) (i : Int) : Prop :=
∀ k k':Nat, 0 ≤ k → k ≤ i → i < k' → k' < a.data.size →
(a.data[k]!)[1]! ≤ (a.data[k']!)[1]!
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def bubble_sort (a : Array2D Int) : Array2D Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem bubble_sort_spec (a : Array2D Int) :
sorted (bubble_sort a) 0 (a.data.size - 1) :=
sorry
-- </vc-theorems>