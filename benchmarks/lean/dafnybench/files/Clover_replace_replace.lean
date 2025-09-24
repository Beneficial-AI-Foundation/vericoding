-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def replace (arr : Array Int) (k : Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem replace_spec (arr : Array Int) (k : Int) (i : Nat) :
i < arr.size →
let result := replace arr k
(arr[i]! > k → result[i]! = -1) ∧
(arr[i]! ≤ k → result[i]! = arr[i]!) :=
sorry
-- </vc-theorems>