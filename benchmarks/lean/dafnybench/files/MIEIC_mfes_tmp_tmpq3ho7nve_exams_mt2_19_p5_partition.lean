-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def partition (a : Array Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem partition_spec (a : Array Int) :
a.size > 0 →
let pivotPos := partition a
0 ≤ pivotPos ∧ pivotPos < a.size ∧
(∀ i:Nat, 0 ≤ i ∧ i < pivotPos → a[i]! < a[pivotPos.toNat]!) ∧
(∀ i:Nat, pivotPos < i ∧ i < a.size → a[i]! ≥ a[pivotPos.toNat]!) :=
sorry
-- </vc-theorems>