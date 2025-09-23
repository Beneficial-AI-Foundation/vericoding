-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def swap (arr : Array Int) (i j : Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem swap_spec (arr : Array Int) (i j : Int) :
0 ≤ i ∧ i < arr.size ∧ 0 ≤ j ∧ j < arr.size →
let arr' := swap arr i j
(arr'[i.toNat]! = arr[j.toNat]! ∧
arr'[j.toNat]! = arr[i.toNat]! ∧
∀ k, 0 ≤ k ∧ k < arr.size ∧ k ≠ i.toNat ∧ k ≠ j.toNat → arr'[k]! = arr[k]!) :=
sorry
-- </vc-theorems>