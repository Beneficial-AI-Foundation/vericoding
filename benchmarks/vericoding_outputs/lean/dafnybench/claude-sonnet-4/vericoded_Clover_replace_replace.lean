import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>

-- </vc-helpers>

-- <vc-definitions>
def replace (arr : Array Int) (k : Int) : Array Int :=
arr.map (fun x => if x > k then -1 else x)
-- </vc-definitions>

-- <vc-theorems>
theorem replace_spec (arr : Array Int) (k : Int) (i : Nat) :
i < arr.size →
let result := replace arr k
(arr[i]! > k → result[i]! = -1) ∧
(arr[i]! ≤ k → result[i]! = arr[i]!) :=
by
  intro h
  constructor
  · intro h_gt
    simp_all [replace]
  · intro h_le
    simp_all [replace]
-- </vc-theorems>
