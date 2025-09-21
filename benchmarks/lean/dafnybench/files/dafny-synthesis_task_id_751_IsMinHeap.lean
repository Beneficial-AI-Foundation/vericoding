-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def IsMinHeap (a : Array Int) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem IsMinHeap_spec (a : Array Int) (result : Bool) :
result → (∀ i, 0 ≤ i ∧ i < a.size / 2 →
a[i]! ≤ a[2*i + 1]! ∧
(2*i + 2 = a.size ∨ a[i]! ≤ a[2*i + 2]!)) ∧
(¬result → ∃ i, 0 ≤ i ∧ i < a.size / 2 ∧
(a[i]! > a[2*i + 1]! ∨
(2*i + 2 ≠ a.size ∧ a[i]! > a[2*i + 2]!))) :=
sorry
-- </vc-theorems>