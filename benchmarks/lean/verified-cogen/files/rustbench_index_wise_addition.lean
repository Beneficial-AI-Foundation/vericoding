-- <vc-preamble>
-- Precondition definitions
@[reducible, simp]
def indexWiseAddition_precond (a : Array (Array Int)) (b : Array (Array Int)) : Prop :=
  a.size = b.size ∧
  (∀ i, i < a.size → a[i]!.size = b[i]!.size) ∧
  (∀ i, i < a.size → ∀ j, j < a[i]!.size → a[i]![j]! + b[i]![j]! ≤ 2147483647) ∧
  (∀ i, i < a.size → ∀ j, j < a[i]!.size → a[i]![j]! + b[i]![j]! ≥ -2147483648)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

/- Test cases and examples can be added here -/