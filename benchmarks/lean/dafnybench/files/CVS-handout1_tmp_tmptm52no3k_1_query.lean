-- <vc-preamble>
partial def sum (a : Array Int) (i j : Int) : Int :=
if i = j then 0
else a[i.toNat]! + sum a (i+1) j

def is_prefix_sum_for (a c : Array Int) : Prop :=
a.size + 1 = c.size ∧
c[0]! = 0 ∧
∀ i, 0 ≤ i ∧ i < a.size → c[(i+1)]! = c[i]! + a[i]!
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def query (a : Array Int) (i j : Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem query_spec (a : Array Int) (i j : Int) :
0 ≤ i ∧ i ≤ j ∧ j ≤ a.size →
∃ res, res = sum a i j :=
sorry
-- </vc-theorems>