-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def NoDups (a : Array Int) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem NoDups_spec (a : Array Int) :
(∀ j : Int, 0 < j ∧ j < a.size → a[(j-1).toNat]! ≤ a[j.toNat]!) →
(NoDups a ↔ ∀ j : Int, 1 ≤ j ∧ j < a.size → a[(j-1).toNat]! ≠ a[j.toNat]!) :=
sorry
-- </vc-theorems>