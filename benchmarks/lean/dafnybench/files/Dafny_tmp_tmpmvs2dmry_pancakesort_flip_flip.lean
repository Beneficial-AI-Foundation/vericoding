-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def flip_ (a : Array Int) (num : Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem flip_spec (a : Array Int) (num : Int) :
a.size > 0 →
0 ≤ num →
num < a.size →
let a' := flip_ a num
(∀ k, 0 ≤ k ∧ k ≤ num → a'[k.toNat]! = a[(num - k).toNat]!) ∧
(∀ k, num < k ∧ k < a.size → a'[k.toNat]! = a[k.toNat]!) :=
sorry
-- </vc-theorems>