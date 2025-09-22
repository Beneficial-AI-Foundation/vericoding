-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def FindZero (a : Array Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem FindZero_spec (a : Array Int) :
(∀ i : Nat, i < a.size → 0 ≤ a[i]!) →
(∀ i : Nat, 0 < i ∧ i < a.size → (a[i]!) - 1 ≤ a[i]!) →
let index := FindZero a
(index < 0 → (∀ i : Nat, i < a.size → a[i]! ≠ 0)) ∧
(0 ≤ index → index < a.size ∧ a[index.toNat]! = 0) :=
sorry
-- </vc-theorems>