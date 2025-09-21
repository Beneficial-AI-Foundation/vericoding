-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def FindPositionOfElement (a : Array Int) (Element : Nat) (n1 : Nat) (s1 : Array Int) :
Int × Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem FindPositionOfElement_spec
(a : Array Int) (Element : Nat) (n1 : Nat) (s1 : Array Int) :
(n1 = s1.size ∧ 0 ≤ n1 ∧ n1 ≤ a.size) →
(∀ i, 0 ≤ i ∧ i < s1.size → a[i]! = s1[i]!) →
let (Position, Count) := FindPositionOfElement a Element n1 s1
(Position = -1 ∨ Position ≥ 1) ∧
(s1.size ≠ 0 ∧ Position ≥ 1 → ∃ i, 0 ≤ i ∧ i < s1.size ∧ s1[i]! = Element) :=
sorry
-- </vc-theorems>