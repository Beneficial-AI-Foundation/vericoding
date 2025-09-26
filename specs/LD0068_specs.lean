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
(∃ i, 0 ≤ i ∧ i < a.size ∧ a[i]! = e) →
let n := LinearSearch a e
(0 ≤ n ∧ n < a.size ∧ a[n.toNat]! = e) ∧
(∀ k, 0 ≤ k ∧ k < n → a[k.toNat]! ≠ e) :=
sorry
-- </vc-theorems>