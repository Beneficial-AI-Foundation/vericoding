-- <vc-preamble>
partial def sum (a : Array Int) (i : Nat) : Int :=
if i == 0 then
a[0]!
else
a[i]! + sum a (i - 1)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def cumsum (a b : Array Int) : Unit :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sum_spec (a : Array Int) (i : Nat) :
0 ≤ i ∧ i < a.size → sum a i = a[i]! + (if i == 0 then 0 else sum a (i - 1)) :=
sorry

theorem cumsum_spec (a b : Array Int) :
a.size == b.size ∧ a.size > 0 ∧ a ≠ b →
(∀ i : Nat, i < a.size → b[i]! = sum a i) :=
sorry
-- </vc-theorems>