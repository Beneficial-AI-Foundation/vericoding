-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def RemoveElement (s : Array Int) (k : Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem RemoveElement_spec (s : Array Int) (k : Nat) :
0 ≤ k ∧ k < s.size →
let v := RemoveElement s k
v.size = s.size - 1 ∧
(∀ i, 0 ≤ i ∧ i < k → v[i]! = s[i]!) ∧
(∀ i, k ≤ i ∧ i < v.size → v[i]! = s[i + 1]!) :=
sorry
-- </vc-theorems>