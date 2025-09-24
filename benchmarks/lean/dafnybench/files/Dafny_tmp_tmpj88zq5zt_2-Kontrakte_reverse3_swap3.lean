-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def swap3 (a : Array Int) (h i j : Nat) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem swap3_spec (a : Array Int) (h i j : Nat) :
0 ≤ h ∧ h < a.size ∧
0 ≤ i ∧ i < a.size ∧
0 ≤ j ∧ j < a.size ∧
i ≠ j ∧ j ≠ h ∧ h ≠ i →
let a' := swap3 a h i j
(a'[h]! = a[i]!) ∧
(a'[j]! = a[h]!) ∧
(a'[i]! = a[j]!) ∧
(∀ k, 0 ≤ k ∧ k < a.size ∧ k ≠ h ∧ k ≠ i ∧ k ≠ j → a'[k]! = a[k]!) :=
sorry
-- </vc-theorems>