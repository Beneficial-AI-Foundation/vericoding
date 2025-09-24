-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max (a : Array Int) (b : Array Int) (i : Nat) (j : Nat) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem max_spec (a : Array Int) (b : Array Int) (i : Nat) (j : Nat) (m : Int) :
(0 ≤ i ∧ i < a.size) →
(0 ≤ j ∧ j < b.size) →
((a[i]! > b[j]! → m = a[i]!) ∧
(a[i]! ≤ b[j]! → m = b[j]!)) :=
sorry
-- </vc-theorems>