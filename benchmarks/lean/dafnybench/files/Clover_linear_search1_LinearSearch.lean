-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def LinearSearch (a : Array Int) (e : Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem LinearSearch_spec (a : Array Int) (e : Int) :
let n := LinearSearch a e
0 ≤ n ∧ n ≤ a.size ∧
(n = a.size ∨ a[n.toNat]! = e) ∧
(∀ i, 0 ≤ i ∧ i < n → e ≠ a[i.toNat]!) :=
sorry
-- </vc-theorems>