-- <vc-preamble>
partial def sum (a : Array Int) (i j : Int) : Int :=
if i = j then 0
else a[(j-1).toNat]! + sum a i (j-1)
def is_prefix_sum_for (a c : Array Int) : Prop :=
a.size + 1 = c.size ∧
∀ i, 0 ≤ i ∧ i ≤ a.size → c[i]! = sum a 0 i
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def queryFast (a c : Array Int) (i j : Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem queryFast_spec (a c : Array Int) (i j : Int) :
0 ≤ i → i ≤ j → j ≤ a.size →
is_prefix_sum_for a c →
queryFast a c i j = sum a i j :=
sorry
-- </vc-theorems>