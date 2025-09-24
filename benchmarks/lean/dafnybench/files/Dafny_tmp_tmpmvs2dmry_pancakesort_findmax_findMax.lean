-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def findMax (a : Array Int) (n : Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem findMax_spec (a : Array Int) (n : Int) :
a.size > 0 →
0 < n ∧ n ≤ a.size →
let r := findMax a n
0 ≤ r ∧ r < n ∧ n ≤ a.size ∧
(∀ k, 0 ≤ k ∧ k < n ∧ n ≤ a.size → a[r.toNat]! ≥ a[k.toNat]!) :=
sorry
-- </vc-theorems>