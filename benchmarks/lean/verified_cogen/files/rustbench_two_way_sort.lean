-- <vc-preamble>
@[reducible, simp]
def twoWaySort_precond (a : Array Bool) : Prop :=
  a.size ≤ 100000
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def twoWaySort (a : Array Bool) (h_precond : twoWaySort_precond a) : Array Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def twoWaySort_postcond (a_old : Array Bool) (result : Array Bool) (h_precond : twoWaySort_precond a_old) : Prop :=
  result.size = a_old.size ∧ 
  result.toList.count true = a_old.toList.count true ∧
  result.toList.count false = a_old.toList.count false ∧
  ∀ i j, 0 ≤ i → i < j → j < result.size → ¬result[i]! ∨ result[j]!

theorem twoWaySort_spec_satisfied (a : Array Bool) (h_precond : twoWaySort_precond a) :
    twoWaySort_postcond a (twoWaySort a h_precond) h_precond := by
  sorry
-- </vc-theorems>