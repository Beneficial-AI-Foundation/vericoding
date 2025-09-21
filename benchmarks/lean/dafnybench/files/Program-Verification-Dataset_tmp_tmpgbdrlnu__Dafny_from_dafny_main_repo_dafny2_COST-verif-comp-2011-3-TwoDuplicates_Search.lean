-- <vc-preamble>
def IsPrefixDuplicate (a : Array Int) (k : Int) (p : Int) : Prop :=
∃ i j, 0 ≤ i ∧ i < j ∧ j < k ∧ a[i.toNat]! = p ∧ a[j.toNat]! = p
def IsDuplicate (a : Array Int) (p : Int) : Prop :=
IsPrefixDuplicate a a.size p
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Search (a : Array Int) : (Int × Int) :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem Search_spec (a : Array Int) :
(4 ≤ a.size) →
(∃ p q, p ≠ q ∧ IsDuplicate a p ∧ IsDuplicate a q) →
(∀ i, 0 ≤ i ∧ i < a.size → 0 ≤ a[i]! ∧ a[i]! < a.size - 2) →
let (p, q) := Search a
p ≠ q ∧ IsDuplicate a p ∧ IsDuplicate a q :=
sorry
-- </vc-theorems>