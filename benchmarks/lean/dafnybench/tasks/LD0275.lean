-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def lookForMin (a : Array Int) (i : Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem lookForMin_spec (a : Array Int) (i : Nat) :
0 ≤ i ∧ i < a.size →
let m := lookForMin a i
i ≤ m ∧ m < a.size ∧
(∀ k, i ≤ k ∧ k < a.size → a[k]! ≥ a[m]!) :=
sorry
-- </vc-theorems>