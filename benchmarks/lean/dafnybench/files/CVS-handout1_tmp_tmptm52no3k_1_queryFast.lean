-- <vc-preamble>
partial def sum (a : Array Int) (i j : Int) : Int :=
if i = j then 0
else a[i.toNat]! + sum a (i+1) j

def is_prefix_sum_for (a c : Array Int) : Prop :=
c.size = a.size + 1 ∧
c[0]! = 0 ∧
∀ i, 0 ≤ i ∧ i < a.size → c[(i+1)]! = c[i]! + a[i]!
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def queryFast (a c : Array Int) (i j : Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem queryFast_spec (a c : Array Int) (i j : Int) :
c.size = a.size + 1 →
c[0]! = 0 →
0 ≤ i →
i ≤ j →
j ≤ a.size →
is_prefix_sum_for a c →
∃ r, r = sum a i j :=
sorry
-- </vc-theorems>