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

-- <vc-definitions>
def indexWiseAddition (a : Array (Array Int)) (b : Array (Array Int)) (h_precond : indexWiseAddition_precond a b) : Array (Array Int) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def indexWiseAddition_postcond (a : Array (Array Int)) (b : Array (Array Int)) (c : Array (Array Int)) (h_precond : indexWiseAddition_precond a b) : Prop :=
  c.size = a.size ∧
  (∀ i, i < c.size → c[i]!.size = a[i]!.size) ∧
  (∀ i, i < c.size → ∀ j, j < c[i]!.size → c[i]![j]! = a[i]![j]! + b[i]![j]!)

theorem indexWiseAddition_spec_satisfied (a : Array (Array Int)) (b : Array (Array Int)) (h_precond : indexWiseAddition_precond a b) :
    indexWiseAddition_postcond a b (indexWiseAddition a b h_precond) h_precond := by
  sorry
-- </vc-theorems>