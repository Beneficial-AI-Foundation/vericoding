-- <vc-preamble>
def Preserved (a : Array Int) (old_a : Array Int) (left right : Nat) : Prop :=
left ≤ right ∧ right ≤ a.size ∧
∀ i, left ≤ i ∧ i < right → a[i]! = old_a[i]!
def Ordered (a : Array Int) (left right : Nat) : Prop :=
left ≤ right ∧ right ≤ a.size ∧
∀ i, 0 < left ∧ left ≤ i ∧ i < right →
a[i-1]! ≤ a[i]!
def Sorted (a : Array Int) (old_a : Array Int) : Prop :=
Ordered a 0 a.size ∧ Preserved a old_a 0 a.size
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def SelectionnSort (a : Array Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem SelectionnSort_spec (a : Array Int) :
Sorted (SelectionnSort a) a :=
sorry
-- </vc-theorems>