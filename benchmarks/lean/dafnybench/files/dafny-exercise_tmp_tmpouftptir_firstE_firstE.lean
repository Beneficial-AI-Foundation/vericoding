-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def firstE (a : Array Char) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem firstE_spec (a : Array Char) :
let x := firstE a
(∃ i, 0 ≤ i ∧ i < a.size ∧ a[i]! = 'e') →
(0 ≤ x ∧ x < a.size ∧ a[x.toNat]! = 'e' ∧
∀ i, 0 ≤ i ∧ i < x → a[i.toNat]! ≠ 'e') ∧
(¬∃ i, 0 ≤ i ∧ i < a.size ∧ a[i]! = 'e') →
x = -1 :=
sorry
-- </vc-theorems>